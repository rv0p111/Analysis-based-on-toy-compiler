#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/MCJIT.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/LoopInfo.h"
#include<cstdio>
#include<iostream>
#include <cctype>
#include <sstream>
#include <vector>
#include <map>

using namespace llvm;


//http://llvm-tutorial-cn.readthedocs.io/en/latest/index.html
//为了持有数值
static int Numeric_Val;
//为了持有Identifier字符串名字
static std::string Identifier_string;
//持有当前token(来自词法分析器)的静态全局变量
static int Current_token;
//用map来存储运算符的优先级
//二元表达式的解析器在按顺序决定LHS和RHS的时候需要知道二元运算符的优先级，所以可以用STL中的map来表示
static std::map<char,int>Operator_Precedence;
//线程上下文
static LLVMContext MyGlobalContext;
//定义全局静态变量管理函数
static legacy::FunctionPassManager * Global_FP;

//定义一个执行引擎作为全局的静态变量
static ExecutionEngine *TheExecutionEngine;

//Module_Ob模块包含了代码中的所有函数和变量
static Module *Module_Ob;
//Builder对象帮助生成LLVM IR 并且记录程序的当前点，以插入LLVM指令，以及Builder对象有创建新指令的函数
//http://www.ithov.com/linux/118240_3.shtml
/*
 能实际提供 API 来创建 LLVM 指令并将这些指令插入基础块的类：IRBuilder 类
 */
static IRBuilder<> Builder(MyGlobalContext);
//Named_Values map对象是记录当前作用域中的所有已定义的值，充当符号表的功能，对于TOY语言来说这个map会包含函数参数信息
static std::map<std::string,Value *>Named_Values;

FILE * file;
enum Token_Type {
    EOF_TOKEN = 0,
    NUMERIC_TOKEN,
    IDENTIFIER_TOKEN,
    LEFT_PARAN_TOKEN,
    RIGHT_PARAN_TOKEN,
    DEF_TOKEN,
    COMMA_TOKEN,
    IF_TOKEN,
    THEN_TOKEN,
    ELSE_TOKEN,
    FOR_TOKEN,
    IN_TOKEN,
    //二元运算符
    BINARY_TOKEN,
    //一元运算符
    UNARY_TOKEN
};
//初始化优先级的函数，把优先级的数值存储在map当中
static void init_precedence()
{
    Operator_Precedence['<'] = 10;
    Operator_Precedence['-'] = 20;
    Operator_Precedence['+'] = 30;
    Operator_Precedence['/'] = 40;
    Operator_Precedence['*'] = 50;
}
//设置一个辅助函数，以返回已定义的二元运算符的优先级
static int getBinOpprecedence()
{
    //判断是不是在ASCII当中
    if(!isascii(Current_token))
    return -1;
    //获取优先级
    int TokPrec = Operator_Precedence[Current_token];
    //判断优先级如果是小于与等于0就报错了
    if(TokPrec<=0) return -1;
    //返回优先级
    return TokPrec;
}

//获取token的函数
static int get_token(){
    
    static int LastChar = ' ';
    
    //判断是不是空格
    while (isspace(LastChar)) {
        LastChar = fgetc(file);
    }
    
    //先判断是不是字符
    if(isalpha(LastChar))
    {
        
        Identifier_string = LastChar;
        while(isalnum((LastChar=fgetc(file))))
            Identifier_string+=LastChar;
        
        if(Identifier_string=="def")
        {
            return DEF_TOKEN;
        }
        //判断if字符串，如果是的话就返回IF_TOKEN
        if(Identifier_string=="if")
        {
            return IF_TOKEN;
        }
        //判断then字符串，如果是的话就返回THEN_TOKEN
        if(Identifier_string=="then")
        {
            return THEN_TOKEN;
        }
        //判断ELSE_TOKEN
        if(Identifier_string=="else")
        {
            return ELSE_TOKEN;
        }
        if(Identifier_string=="for")
        {
            return FOR_TOKEN;
        }
        if(Identifier_string=="in")
        {
            return IN_TOKEN;
        }
        //返回二元运算符
        if (Identifier_string=="binary") {
            
            return BINARY_TOKEN;
        }
        if(Identifier_string=="unary")
        {
            return UNARY_TOKEN;
        }
        return IDENTIFIER_TOKEN;
    }
    //判断是不是数字
    if(isdigit(LastChar))
    {
        std::string NumStr;
        
        //设置两个标记，其中flag1表示的就是第一个是数字了然后就设置flag1=1，然后接下来就是去判断
        //如果flag1=1了，下一个是不是小数点，如果是就继续，但是如果当一件出现过一次小数点了再去出现
        //就直接返回那个字符，也就是分析不出token，不会返回NUMERIC_TOKEN
        int flag1 = 0;
        int flag2 = 0;
        do{
            NumStr+=LastChar;
            LastChar = fgetc(file);
            
            //判断如果在数字后面出现过小数点了，这里还出现小数点就直接返回
            if(flag2==1&&LastChar=='.')
            {
                int ThisChar = LastChar;
                LastChar = fgetc(file);
                return ThisChar;
            }
            //刚进入循环就直接设置flag1=1了，因为第一个就是数字
            if(flag1==0)
            {
                flag1=1;
            }
            //判断前面已经有数字的情况下出现小数点就设置flag2为1
            if(flag1==1&&LastChar=='.')
            {
                flag2=1;
            }
        
        }while(isdigit(LastChar)|| LastChar == '.');
        
        //strtod是C语言及C++中的重要函数，功能是将字符串转换成浮点数，表头文件是#include <stdlib.h>，相关函数有atoi，atol，strtod，strtol。
        Numeric_Val = strtod(NumStr.c_str(), 0);
        
        return NUMERIC_TOKEN;
    }
    //    if(LastChar == '(')
    //    {
    //        LastChar = fgetc(file);
    //        return LEFT_PARAN_TOKEN;
    //    }
    //    if(LastChar == ')')
    //    {
    //         LastChar = fgetc(file);
    //        return RIGHT_PARAN_TOKEN;
    //    }
    //    if(LastChar==',')
    //    {
    //        LastChar = fgetc(file);
    //        return COMMA_TOKEN;
    //    }
    if(LastChar=='#')
    {
        LastChar = fgetc(file);
        while (LastChar!=EOF && LastChar !='\n' &&LastChar != '\r');
        if(LastChar!=EOF)
            return get_token();
    }
    
    if(LastChar==EOF)
        return EOF_TOKEN;
    
    int ThisChar = LastChar;
    LastChar = fgetc(file);
    return ThisChar;
}

/**
 由词法分析器得到的token的各种信息由AST这一个数据结构来存储，这些信息包含在语法分析器的逻辑当中，并且根据当前解析的token类型来填充AST
 */
//每一个AST类都需要包含Codegen()函数，函数的返回值是LLVM Value对象，它表示了静态单赋值(SSA)对象，每个变量仅赋值一次，在Codegen过程当中还需要定义几个静态对象
//定义一个base类解析表达式
class BaseAST{
    public:
    //虚函数析构函数
    virtual ~BaseAST(){};
    //这是一个非常重要的LLVM类。它是程序计算的所有值的基类，可以用作其他值的操作数。Value是其他重要类如指令和函数的超类。所有值都有一个类型。类型不是值的子类。一些值可以有一个名称，它们属于某个模块。在值上设置名称将自动更新模块的符号表。每个值都有一个“使用列表”，用于跟踪哪些其他值正在使用这个值。一个值还可以有任意数量的ValueHandle对象，这些对象监视它并侦听RAUW并销毁事件。
    //声明纯虚函数的一般形式是 virtual 函数类型 函数名 (参数表列) =0;
    //它只起形式上的作用，告诉编译系统“这是纯虚函数”
    virtual Value * Codegen()=0;
};
//为for循环去定义AST
class ExprForAST : public BaseAST {
    //定义变量标识
    std::string Var_Name;
    //这里是定义的Start、End、Step、Body的结构，可能是表达式也可能是数字也可能是字母等，所以用BaseAST去表示
    BaseAST *Start, *End, *Step, *Body;
    
public:
    ExprForAST(const std::string &varname, BaseAST *start, BaseAST *end,
               BaseAST *step, BaseAST *body)
    : Var_Name(varname), Start(start), End(end), Step(step), Body(body) {}
    Value *Codegen() override;
};

//定义if表达式的AST节点
class ExprIfAST : public BaseAST {
    //关于Cond、Then、Else的AST节点
    BaseAST *Cond, *Then, *Else;
    
public:
    //构造方法
    ExprIfAST(BaseAST *cond, BaseAST *then, BaseAST *else_st)
    : Cond(cond), Then(then), Else(else_st) {}
    //需要去重写Codegen构造函数
    Value *Codegen() override;
};

//变量表达式
class VariableAST :public BaseAST
{
    std::string Var_Name;
    //定义string对象用作存储变量名
    public:
    //变量AST类的含参构造函数由传入构造函数的字符串进行初始化
    VariableAST (std::string &name) :Var_Name(name){}
    virtual Value * Codegen();
};
//语言会包括一些数值表达式，数值表达式的AST类定义如下所示
class NumericAST :public BaseAST{
    int numeric_val;
    public:
    NumericAST(int val):numeric_val(val){}
    virtual Value * Codegen();
};
//一元表达式的AST结构
class ExprUnaryAST : public BaseAST {
    char Opcode;
    BaseAST *Operand;
    
public:
    ExprUnaryAST(char opcode, BaseAST *operand)
    : Opcode(opcode), Operand(operand) {}
    Value *Codegen() override;
};
//二元表达式的AST结构
class BinaryAST:public BaseAST{
    
    //用于存储二元运算符的string对象
    std::string Bin_Operator;
    //用于存储一个二元表达式的LHS和RHS的对象，由于LHS和RHS二元操作可以是任何类型，因此用BaseAST对象存储
    BaseAST *LHS,*RHS;
    public:
    //初始化二元运算符，二元表达式的LHS和RHS
    BinaryAST (std::string op,BaseAST *lhs,BaseAST *rhs):Bin_Operator(op),LHS(lhs),RHS(rhs){}
    virtual Value *Codegen();
};

//函数声明的AST类定义
//vector的元素不仅仅可以是int,double,string,还可以是结构体，但是要注意：结构体要定义为全局的，否则会出错。
class FunctionDeclAST
{
    //函数名
    std::string Func_Name;
    //参数列表
    std::vector<std::string> Arguments;
    //是否是运算符
    bool isOperator;
    
    //优先级
    unsigned Precedence;
    
    public:
    FunctionDeclAST(const std::string &name,const std::vector<std::string> &args,bool isoperator = false,unsigned prec = 0):Func_Name(name),Arguments(args),isOperator(isoperator),Precedence(prec){}
    //获取一元运算符的名字
    bool isUnaryOp() const {return isOperator && Arguments.size()==1;}
    //获取二元运算符的名字
    bool isBinaryOp() const {return isOperator && Arguments.size() == 2;}
    
    //获取操作符的名字
    char getOperatorName() const {
        assert(isUnaryOp() || isBinaryOp());
        return Func_Name[Func_Name.size()-1];
    }
    
    //返回优先级的函数
    unsigned getBinaryPrecedence() const {
        return Precedence;
    }
    Function *Codegen();
};
//用于函数定义的AST类的定义如下所示
class FunctionDefnAST {
    FunctionDeclAST * Func_Decl;
    BaseAST * Body;
    public:
    FunctionDefnAST(FunctionDeclAST *proto,BaseAST *body):Func_Decl(proto),Body(body){}
    Function *Codegen();
};
//用于函数调用的AST类的定义如下所示
class FunctionCallAST:public BaseAST{
    std::string Function_Callee;
    std::vector<BaseAST *> Function_Arguments;
    public:
    FunctionCallAST(const std::string &callee,std::vector<BaseAST *>&args):Function_Callee(callee),Function_Arguments(args){}
    virtual Value *Codegen();
};
static BaseAST * Base_Parser();
//从词法分析器的输入流获得下一个token
static int next_token(){
    Current_token = get_token();
    return Current_token;
}
//一元表达式的解析
static BaseAST *unary_parser() {
    if (!isascii(Current_token) || Current_token == '(' || Current_token == ',')
        return Base_Parser();
    
    int Op = Current_token;
    next_token();
    if (BaseAST *Operand = unary_parser())
        return new ExprUnaryAST(Op, Operand);
    return 0;
}

//解析binary运算符的解析器
//它的参数包括一个整数和一个指针，其中整数代表运算符优先级，指针则指向当前已解析出来的那部分表达式
//传入binary_op_parser的优先级表示的是该函数所能处理的最低运算符优先级
static BaseAST *binary_op_parser(int Old_Prec,BaseAST *LHS)
{
    //循环递归分析
    while (1) {
        //获取操作符的优先级
        int Operator_Prec = getBinOpprecedence();
        
        //判断操作符的优先级和旧的相比，还小于就直接返回
        if(Operator_Prec < Old_Prec)
        return LHS;
        
        //获取运算符
        int BinOp = Current_token;
        
        //读取下一个token
        next_token();
        
        //LHS和RHS都是可以用来存储一个二元表达式，所以又要根据token去处理
        BaseAST *RHS = Base_Parser();
        
        //如果RHS没有构造成功就直接return 0
        if(!RHS) return 0;
        
        //当前优先级和之前运算符的优先级是一起被检查的，输出则取决于二元运算符的LHS和RHS，这里需要注意的是二元运算符解析器是递归调用的，因为RHS可以是一个表达式，而不只是一个单独的标识符
        int Next_Prec = getBinOpprecedence();
        
        /*表达式的左侧和RHS序列中第一对都已经解析完毕，该考虑表达式的结合次序了。路有两条，要么选择“(a+b) binop unparsed”，要么选择“a + (b binop unparsed)”。为了搞清楚到底该怎么走，我们先预读出“binop”，查出它的优先级，再将之与BinOp（本例中是“+”）的优先级相比较：*/
        /*
         binop位于“RHS”的右侧，如果binop的优先级低于或等于当前运算符的优先级，则可知括号应该加在前面，即按“(a+b) binop ...”处理。在本例中，当前运算符是“+”，下一个运算符也是“+”，二者的优先级相同。既然如此，理应按照“a+b”来构造AST节点
         */
        if(Operator_Prec < Next_Prec)
        {
            //传入的运算符的优先级需要+1，也就是说如果还要看右边的，右边先算的话就要比当前运算符要大
            /*
             看一下主表达式右侧的二元运算符，我们发现它的优先级比当前正在解析的binop的优先级要高。由此可知，如果自binop以右的若干个连续有序对都含有优先级高于“+”的运算符，那么就应该把它们全部解析出来，拼成“RHS”后返回。为此，我们将最低优先级设为“TokPrec+1”，递归调用函数“ParseBinOpRHS”。该调用会完整解析出上述示例中的“(c+d)*e*f”，并返回构造出的AST节点，这个节点就是“+”表达式右侧的RHS。
             */
            RHS = binary_op_parser(Operator_Prec+1, RHS);
            
            if(RHS==0) return 0;
        }
        //解析有序对列表
        LHS = new BinaryAST(std::to_string(BinOp),LHS,RHS);
    }
}
//解析表达式的
static BaseAST * expression_parser();

//为if/then/else结构定义解析逻辑
static BaseAST *If_parser() {
    
    //读取下一个字符，因为当前的Current_token是If_token，所以需要读入下一个
    next_token();
    
    //解析if的表达式，返回值类型是BinaryAST
    BaseAST *Cond = expression_parser();
    if (!Cond)
        return 0;
    
    if (Current_token != THEN_TOKEN)
        return 0;
    //读取下一个字符
    next_token();
    //解析then的表达式
    BaseAST *Then = expression_parser();
    if (Then == 0)
        return 0;
    
    //判断当前的TOKEN是不是ELSE_TOKEN
    if (Current_token != ELSE_TOKEN)
        return 0;
    
    //读取下一个字符
    next_token();
    
    BaseAST *Else = expression_parser();
    if (!Else)
        return 0;
    
    return new ExprIfAST(Cond, Then, Else);
}


//关于括号的函数定义，调用这个函数的时候就是在泛型函数当中Base_Parser函数当中
static BaseAST *paran_passer(){
    //读取下一个表达式，因为前面已经是一个'('已经读取了
    next_token();
    
    //解析表达式
    BaseAST *V = expression_parser();
    //判断表达式
    if(!V)
    return 0;
    //到了最后一个右边括号
    if(Current_token != ')')
    return 0;
    
    return V;
}

//定义下面的numeric_parser函数去解析数值表达式
static BaseAST * numeric_parser(){
    BaseAST * result = new NumericAST(Numeric_Val);
    next_token();
    return result;
}

//定义parser函数来解析标识符表达式，需要注意的是标识符可以是变量引用或者是函数调用，它们之间通过函数调用会由括号这一特征来区分
static BaseAST *identifier_parser(){
    //获取标识符
    std::string IdName = Identifier_string;
    //已知1个token的情况下获取下一个token
    next_token();
    
    //表示就是标识符
    if(Current_token!='(')
    return new VariableAST(IdName);
    
    //继续获取下一个
    next_token();
    
    std::vector<BaseAST *>Args;
    if(Current_token!=')')
    {
        while (1) {
            BaseAST * Arg = expression_parser();
            if(!Arg) return 0;
            Args.push_back(Arg);
            //判断当前的符号是不是)，如果是的话说明函数调用结束
            if(Current_token == ')') break;
            //如果下一个参数的间隔不是,那就说明错误了
            if(Current_token !=',')
            return 0;
            //继续读取下一个参数
            next_token();
        }
    }
    
    next_token();
    //返回函数调用的AST
    return new FunctionCallAST(IdName,Args);
}

 //在for标识符确定为FOR_TOKEN的时候就会走这个方法，for结构的分析方法
static BaseAST *For_parser() {
    
    next_token();
    
    //然后就是分析是否是标识符也就是i这个条件比如i=1，这个i就是这个标识符
    if (Current_token != IDENTIFIER_TOKEN)
        return 0;
    
    std::string IdName = Identifier_string;
    next_token();
    
    //这里判断的相当于就是初始条件下的'='号，也就是i=1的等于号
    if (Current_token != '=')
        return 0;
    //然后读取下一个
    next_token();
    //然后解析开始的表达式就是i=1当中的1可能是1也可能是表达式
    BaseAST *Start = expression_parser();
    if (Start == 0)
        return 0;
    //然后就是去判断逗号
    if (Current_token != ',')
        return 0;
    //再读取下一个
    next_token();
    //判断结束标识符，就比如说i<n
    BaseAST *End = expression_parser();
    if (End == 0)
        return 0;
    
    BaseAST *Step = 0;
    //然后判断逗号
    if (Current_token == ',') {
        next_token();
        //判断步长，可以是表达式，所以调用的就是expression_parser方法
        Step = expression_parser();
        if (Step == 0)
            return 0;
    }
    
    //判断还不是in标识符
    if (Current_token != IN_TOKEN)
        return 0;
    next_token();
    //生成函数体的AST结构
    BaseAST *Body = expression_parser();
    if (Body == 0)
        return 0;
    
    return new ExprForAST(IdName, Start, End, Step, Body);
}

//定义泛型函数，来根据由词法分析器确定的token类型的调用特定解析函数
//输入流被词法分析器构建成token流并且传递给语法分析器，Current_token持有当前处理的token，在这一阶段token类型是已知的，并且根据其类型来调用相应的解析函数来初始化AST
static BaseAST * Base_Parser(){
    
    switch (Current_token) {
        default:return 0;
        case IDENTIFIER_TOKEN: return identifier_parser();
        case NUMERIC_TOKEN: return numeric_parser();
        case '(':return paran_passer();
        //根据IF_TOKEN去返回，说明当前Current_token就是IF_TOKEN
        case IF_TOKEN:return If_parser();
        //根据for
        case FOR_TOKEN:return For_parser();
    }
}

//解析表达式的函数
static BaseAST * expression_parser(){
    //进行左边部分的解析
    BaseAST * LHS = Base_Parser();
    if(!LHS) return 0;
    return binary_op_parser(0,LHS);
}


////只是用来定义函数来解析函数的声明
//static FunctionDeclAST *func_decl_parser(){
//
//    //如果当前的token不是标识符的token，那么就直接返回，因为函数声明前面的就是标识符
//    if(Current_token != IDENTIFIER_TOKEN)
//    return 0;
//
//    //定义标识符
//    std::string FnName = Identifier_string;
//
//    //获取下一个token
//    next_token();
//
//    if(Current_token != '(')
//        return 0;
//
//    //做一个标记，看看第一次是,后面一个是不是,
//    int flag = 0;
//    std::vector<std::string> Function_Argument_Names;
//
//    //然后这里先判断是不是标识符，如果是标识符再进去while循环
//    if(next_token()==IDENTIFIER_TOKEN)
//    {
//        //while循环的条件就是参数得是字母，或者当前的token为,也是可以的
//        while(Current_token==IDENTIFIER_TOKEN||Current_token==',')
//        {
//            if(flag==1&&Current_token==',')
//            {
//                break;
//            }
//            if(Current_token==',')
//            {
//                flag=1;
//            }
//            else
//            {
//                //逗号就不用到加到参数列表当中了
//                Function_Argument_Names.push_back(Identifier_string);
//                flag=0;
//            }
//
//            next_token();
//        }
//
//    }
//    if(Current_token != ')')
//        return 0;
//
//    next_token();
//
//    return new FunctionDeclAST(FnName, Function_Argument_Names);
//}

//拿来也会修改进行解析函数声明的解析器
static FunctionDeclAST *func_decl_parser()
{
    //定义的是函数的名字
    std::string FnName;

    //种类标识码
    unsigned Kind = 0;
    //运算符的优先级
    unsigned BinaryPrecedence = 30;

    //判断当前的token
    switch (Current_token) {
        default:
            return 0;
        //表示是标识符
        case IDENTIFIER_TOKEN:
            //设置标识符
            FnName = Identifier_string;
            //设置种类码
            Kind = 0;
            //读取下一个token
            next_token();
            break;
        //表示是一元标识符
        case UNARY_TOKEN:
            //读取下一个标识
            next_token();
            //判断当前的标识符，是不是在ASCII当中的
            if (!isascii(Current_token))
                return 0;
            //设置unary
            FnName = "unary";
            //再加上之后token
            FnName += (char)Current_token;
            //设置种类码
            Kind = 1;
            //读取下一个token
            next_token();
            break;
        //表示是二元标识符
        case BINARY_TOKEN:
            //读取下一个token
            next_token();
            //判断当前的token在不在ASCII码当中
            if (!isascii(Current_token))
                return 0;
            //设置函数名
            FnName = "binary";
            FnName += (char)Current_token;
            //设置种类码
            Kind = 2;
            //读取下一个token
            next_token();

            if (Current_token == NUMERIC_TOKEN) {
                if (Numeric_Val < 1 || Numeric_Val > 100)
                    return 0;
                //设置优先级
                BinaryPrecedence = (unsigned)Numeric_Val;
                next_token();
            }
            break;
    }

    //判断当前运算符是不是(，如果是的话就返回0
    if (Current_token != '(')
        return 0;

    std::vector<std::string> ArgNames;
    //判断是不是IDENTIFIER_TOKEN，如果是，就放入容器中
    while (next_token() == IDENTIFIER_TOKEN)
        ArgNames.push_back(Identifier_string);

    //判断标识符是不是)如果不是了
    if (Current_token != ')')
        return 0;

    //接着去判断下一个token
    next_token();

    //判断kind和参数的个数是不是一致的
    if (Kind && ArgNames.size() != Kind)
        return 0;

    return new FunctionDeclAST(FnName, ArgNames, Kind != 0, BinaryPrecedence);
}

static FunctionDefnAST *func_defn_parser(){
    next_token();
    //创建函数声明的AST
    FunctionDeclAST * Decl = func_decl_parser();
    //判断Decl
    if(Decl==0) return 0;
    //如果函数实现存在的话
    if(BaseAST * Body = expression_parser())
    return new FunctionDefnAST(Decl,Body);
    
    return 0;
}

Value *ExprIfAST::Codegen() {
    
    //进行条件的代码
    Value *CondV = Cond->Codegen();
    
    if (CondV == 0)
        return 0;
    //https://blog.csdn.net/cteng/article/details/50686514
    //这里生成的就是icmp ne指令就比如说icmp ne i32 %booltmp, 0
    CondV = Builder.CreateICmpNE(
                                 CondV, ConstantInt::get(Type::getInt32Ty(MyGlobalContext), 0), "ifcond");
    
    //在结构良好的LLVM IR中，每条指令都嵌入在一个基本块中。您可以从getParent()获取BasicBlock。getParent()将始终在LLVM IR层次结构中向前走一步，即。您可以从BasicBlock中获得父函数，从函数中得到模块。
    
    //返回当前插入点
    /**
     此代码创建与if/then/else语句相关的基本块，并直接对应于上面示例中的块,下面就是去获取正在构建的当前函数对象。它通过请求构建器获得当前的BasicBlock，并请求该块获得它的“父块”(它当前嵌入的函数)。
     */
    Function *TheFunction = Builder.GetInsertBlock()->getParent();
    
    /*
     一旦它有了这个，它就会创建三个块。注意，它将“TheFunction”传递给“then”块的构造函数。这导致构造函数自动将新块插入到指定函数的末尾。创建了另外两个块，但还没有插入到函数中。
     */
    //创建then的代码块
    BasicBlock *ThenBB =
    BasicBlock::Create(MyGlobalContext, "then", TheFunction);
    
    //创建else的代码块
    BasicBlock *ElseBB = BasicBlock::Create(MyGlobalContext, "else");
    
    //如果指定了父参数，那么基本块将自动插入到函数的末尾(如果InsertBefore是0)，或者在指定的基本块之前。
    //ifcont:块
    BasicBlock *MergeBB = BasicBlock::Create(MyGlobalContext, "ifcont");
    
    /**
     一旦这些块被创建，我们就可以发出在它们之间进行选择的条件分支。注意，创建新块不会隐式地影响IRBuilder，因此它仍然插入到条件进入的块中。还要注意，它正在创建一个分支到“then”块和“else”块，即使“else”块还没有插入到函数中。这都没问题:这是LLVM支持转发引用的标准方式。
     */
    //创建一个有条件的“br Cond, TrueDest, falseDest的指令。
    //br i1 %ifcond, label %then, label %else
    Builder.CreateCondBr(CondV, ThenBB, ElseBB);
    
    /**
     在插入条件分支之后，我们将构建器移动到“then”块中。严格地说，这个调用将插入点移动到指定块的末尾。但是，由于“then”块是空的，它也从在块的开始插入开始，其实就是去设置插入点
     */
    Builder.SetInsertPoint(ThenBB);
    
    //生成Then的IR表示，一旦设置了插入点，我们就递归地将AST中的“then”进行调用Codegen
    //所以我们这里需要先去生成不影响我们phi的设置
    Value *ThenV = Then->Codegen();
    
    if (ThenV == 0)
        return 0;
    
    //为了完成“then”块，我们为merge块创建一个无条件的分支,我们为merge block创建一个无条件的分支
    //就是br label %ifcont这条指令
    Builder.CreateBr(MergeBB);
    
    /*
     下面这一行非常微妙，但非常重要。基本的问题是，当我们在合并块中创建Phi节点时，我们需要设置块/值对，以指示Phi如何工作
     重要的是，Phi节点期望在CFG中为块的每个前身其实就是
     then:                                             ; preds = %entry
     br label %ifcont。
     这里的then就表示是前身
     CFG就是控制流图(Conttol flow graph)是用在编译器的一种抽象的数据结构，它是一个过程或程序的抽象表现，由编译器在内部维护
     为什么，当我们把它设置到上面的5行时，我们得到当前块了吗？
     问题是，“Then” expression本身可能会改变构建器所释放的块，例如，它包含一个嵌套的“if/ Then /else”表达式。因为递归地调用codegen()可以任意改变当前块的概念，所以我们需要为设置Phi节点的代码获取最新的值。
     */
    //Then的codegen可以改变当前的块，在PHI中更新ThenBB
    ThenBB = Builder.GetInsertBlock();
    
    /*
     else”块的代码生成基本上与“then”块的代码生成相同。唯一显著的区别是第一行，它将“else”块添加到函数中。还记得之前创建了“else”块，但没有添加到函数中。既然已经发出了“then”和“else”块，我们就可以用合并代码结束
     */
    TheFunction->getBasicBlockList().push_back(ElseBB);
    
    Builder.SetInsertPoint(ElseBB);
    
    Value *ElseV = Else->Codegen();
    
    if (ElseV == 0)
        return 0;
    
    //创建br指令，也就是br label %ifcont
    Builder.CreateBr(MergeBB);
    
    //获取当前的块
    ElseBB = Builder.GetInsertBlock();
    
    /**
     ifcont:                                           ; preds = %else, %then
     %iftmp = phi i32 [ 1, %then ], [ %addtmp3, %else ]
     ret i32 %iftmp
     }
     */
    //插入MergeBB块：
    /*
     这里的前两行现在很熟悉:首先将“merge”块添加到函数对象(它之前是浮动的，就像上面的else块一样)
     */
    TheFunction->getBasicBlockList().push_back(MergeBB);
    
    /*第二个更改插入点，以便新创建的代码进入merge块。完成之后，我们需要创建节点并为其设置块/值对*/
    Builder.SetInsertPoint(MergeBB);
    
     //分支语句：需要phi merge节点
    PHINode *PN =
    Builder.CreatePHI(Type::getInt32Ty(MyGlobalContext), 2, "iftmp");
    
    //这里就是生产 %iftmp = phi i32 [ 1, %then ], [ %addtmp3, %else ]
    PN->addIncoming(ThenV, ThenBB);
    PN->addIncoming(ElseV, ElseBB);
    
    /*最后，CodeGen函数返回phi节点作为if/then/else表达式计算的值，在上面的示例中，这个返回值将被输入到顶级函数的代码中，该代码将创建返回指令*/
    
    return PN;
}

//为数值变量生成代码的函数定义如下所示
Value *NumericAST::Codegen()
{
    //在LLVM IR当中，整数常量由ConstantInt类表示，它的值由APInt类持有
    return ConstantInt::get(Type::getInt32Ty(MyGlobalContext), numeric_val);
}
//为变量表达式生成代码的函数定义如下所示
Value * VariableAST::Codegen()
{
    Value * V = Named_Values[Var_Name];
    return V ? V:0;
}
//二元表达式的Codegen()函数，如果这里生成了多个addtmp变量，LLVM会自动的为每一个addtmp添加递增的、唯一的数值后缀加以区分
Value *BinaryAST::Codegen(){

    Value * L = LHS->Codegen();
    Value * R = RHS->Codegen();
    
    if(L==0||R==0) return 0;
    //atoi (表示 ascii to integer)是把字符串转换成整型数的一个函数
    //LLVM指令遵循严格的约束：例如，add指令的Left、Right操作数必须同属一个类型，结果的类型则必须与操作数的类型相容
    switch (atoi(Bin_Operator.c_str())) {
        case '+':
            return Builder.CreateAdd(L, R,"addtmp");
        case '-':
            return Builder.CreateSub(L,R, "subtmp");
        case '*':
            return Builder.CreateMul(L,R, "multmp");
        case '/':
            return Builder.CreateUDiv(L,R, "divtmp");
        //表示运算符如果是小于的话
        case '<':
            //生成一个比较指令，icmp”指令根据其两个整数、整数向量、指针或指针向量操作数的比较返回布尔值或布尔值向量。
            //ult表示少于
            //相当于会生成这样的指令%cmptmp = icmp ult i32 %x, %addtmp
            L=Builder.CreateICmpULT(L,R,"cmptmp");
            //生成一个bool指令,“zext”指令接受要转换的值，以及要转换的类型。这两种类型都必须是整数类型，或者是相同数量的整数的向量。该值的位大小必须小于目标类型ty2的位大小。
            //  相当于会生成这样的指令 %booltmp = zext i1 %cmptmp to i32
            return Builder.CreateZExt(L,Type::getInt32Ty(MyGlobalContext),"booltmp");
        default:
            break;
    }
    
    //返回指令所处的函数
    /**
     LLVM Module的符号表中查找函数名。如前文所述，LLVM Module是个容器，待处理的函数全都在里面。只要保证各函数的名字与用户指定的函数名一致，我们就可以利用LLVM的符号表替我们完成函数名的解析
     */
    Function *F = Module_Ob->getFunction(std::string("binary") + Bin_Operator);
    assert(F && "binary operator not found!");
    
    Value *Ops[] = { L, R };
    //传入参数和函数以及指令名字，创建一条LLVM call指令
    return Builder.CreateCall(F, Ops, "binop");
}
//解析函数调用的时候，会递归的对其传递的参数调用Codegen()函数，最后再去创建LLVM调用指令
Value *FunctionCallAST::Codegen()
{
    Function * CalleeF = Module_Ob->getFunction(Function_Callee);
    //函数参数
    std::vector<Value *>ArgsV;
    //遍历函数参数

    for (unsigned i = 0, e = Function_Arguments.size(); i != e; ++i)  {
        ArgsV.push_back(Function_Arguments[i]->Codegen());
    }
    return Builder.CreateCall(CalleeF,ArgsV,"calltmp");
}
//解析if/then/else结构，为其生成LLVM IR的代码

//函数声明的Codegen()
/*
 函数原型的代码生成过程：函数定义和外部函数声明都依赖于它。
 */
/**
 首先需要注意的是该函数的返回值类型是“Function*”而不是“Value*”。“函数原型”描述的是函数的对外接口（而不是某表达式计算出的值），返回代码生成过程中与之相对应的LLVM Function自然也合情合理
 */
Function *FunctionDeclAST::Codegen()
{
    std::vector<Type*>Integers(Arguments.size(),Type::getInt32Ty(MyGlobalContext));
    
    //我们定义函数的参数为int类型，和常数一样，LLVM中的类型对象也是单例，应该用“get”而不是“new”来获取
    //因此第一行创建了一个包含“N”个LLVM int的vector。随后，FunctionType::get方法以这“N”个int为参数类型、以单个int为返回值类型，创建出一个参数个数不可变
    FunctionType * FT = FunctionType::get(Type::getInt32Ty(MyGlobalContext), Integers, false);
    
    /*
     下面实际上创建的是与该函数原型相对应的函数。其中包含了类型、链接方式和函数名等信息，还指定了该函数待插入的模块。“ExternalLinkage”表示该函数可能定义于当前模块之外，且/或可以被当前模块之外的函数调用。Name是用户指定的函数名：如上述代码中的调用所示，既然将函数定义在“TheModule”内，函数名自然也注册在“TheModule”的符号表内。
     */
    Function *F = Function::Create(FT, Function::ExternalLinkage, Func_Name, Module_Ob);
    
    /**
     在这里主要是在处理名称冲突时，Module的符号表与Function的符号表类似：在模块中添加新函数时，如果发现函数名与符号表中现有的名称重复，新函数会被默默地重命名。被重命名过就代表我的名字不一致，那么就要删除相应的函数
     */
    /**在两种情况下允许重定义函数：第一，允许对同一个函数进行多次extern声明，前提是所有声明中的函数原型保持一致（由于只有一种参数类型，我们只需要检查参数的个数是否匹配即可）。第二，允许先对函数进行extern声明，再定义函数体。这样一来，才能定义出相互递归调用的函数。所以我们下面判断名字的时候下面还要去判断参数
     */
    if(F->getName() != Func_Name) {
        
        //调用eraseFunctionParent）将刚刚创建的函数对象删除
        F->eraseFromParent();
        
        //然后调用getFunction获取与函数名相对应的函数对象
        F = Module_Ob->getFunction(Func_Name);
        
        //如果函数体就说明定义过，就返回0，直接拒绝
        if(!F->empty()) return 0;
        //判断还是你的参数如果不等于我们之前构造的数量，那么也直接返回
        if(F->arg_size() != Arguments.size()) return 0;
        
    }
    unsigned Idx = 0;
    
    //遍历函数原型的所有参数，为这些LLVM Argument对象逐一设置参数名，并将这些参数注册倒NamedValues映射表内
    for(Function::arg_iterator Arg_It = F->arg_begin(); Idx != Arguments.size(); ++Arg_It, ++Idx) {
        Arg_It->setName(Arguments[Idx]);
      
        Named_Values[Arguments[Idx]] = Arg_It;
    }
    return F;
}
//函数定义
Function *FunctionDefnAST::Codegen() {
    
      /*生成函数原型（Proto）的代码并进行校验。与此同时，需要清空NamedValues映射表，确保其中不会残留之前代码生成过程中的产生的内容。函数原型的代码生成完毕后，一个现成的LLVM Function对象就到手了。*/
    Named_Values.clear();
    
    //生成函数定义的IR代码，
    Function *TheFunction = Func_Decl->Codegen();
    
    if(TheFunction == 0) return 0;
    
    //根据函数声明的AST结构里面的BinaryOp设置
    if (Func_Decl->isBinaryOp()) {
        Operator_Precedence[Func_Decl->getOperatorName()] = Func_Decl->getBinaryPrecedence();
    }
    /*
     模块（Module），函数（Function），代码块（BasicBlock），指令（Instruction）
     模块包含了函数，函数又包含了代码块，后者又是由指令组成。除了模块以外，所有结构都是从值产生而来的。
     */
    //新建了一个名为“entry”的基本块对象，稍后该对象将被插入TheFunction
    BasicBlock *BB = BasicBlock::Create(MyGlobalContext,"entry", TheFunction);
    
    //插入BasicBlock 代码块，告诉Builder，后续的新指令应该插至刚刚新建的基本块的末尾处。
    //builder.setInsertPoint 会告知 LLVM 引擎接下来将指令插入何处，简而言之，它指定创建的指令应该附加到指定块的末尾
    Builder.SetInsertPoint(BB);
    
    //现在该开始设置Builder对象了。LLVM基本块是用于定义控制流图（Control Flow Graph）的重要部件。当前我们还不涉及到控制流，所以所有的函数都只有一个基本块
    //函数体产生
    if(Value *RetVal = Body->Codegen()) {
        
        //创建一个ret指令，如果我们增加了if-then-else的话，这里返回的RetVal就是Phi类型的
        /**
         ifcont:                                           ; preds = %else, %then
         %iftmp = phi i32 [ 1, %then ], [ %addtmp, %else ]
         ret i32 %iftmp
         }
         */
        Builder.CreateRet(RetVal);
        //验证生成的代码，检查一致性。
        //简单检查一个函数的错误，在调试一个pass时有用。如果没有错误，函数返回false。如果发现错误，则向OS(如果非空)写入描述错误的消息，并返回true。
        verifyFunction(*TheFunction);
        //使用PassManager的run方法就可以进行优化
        
        //安排Pass进行执行，跟踪是否有任何传递修改函数，如果有，返回true。
       Global_FP->run(*TheFunction);
        
        return TheFunction;
    }
    //Error reading body, remove function.
    //错误读取函数体，所以删除函数
    TheFunction->eraseFromParent();
    
    if(Func_Decl->isBinaryOp())
        Operator_Precedence.erase(Func_Decl->getOperatorName());
    return 0;
}
//封装上层函数
static void HandleDefn(){
    if(FunctionDefnAST * F = func_defn_parser())
    {
        if(Function * LF = F->Codegen())
        {
            
        }
    }
    else
    {
        next_token();
    }
}
//这里主要做的就是顶层
static FunctionDefnAST *top_level_parser() {
    
    //解析二元表达式作为函数体
    if(BaseAST* E = expression_parser()) {
        //构造函数声明
        FunctionDeclAST *Func_Decl = new FunctionDeclAST("", std::vector<std::string>());
        //返回的是一整个函数的定义
        return new FunctionDefnAST(Func_Decl, E);
    }
    return 0;
}
////一元表达式的Codegen生成
//Value *ExprUnaryAST::Codegen() {
//    Value *OperandV = Operand->Codegen();
//    if (OperandV == 0)
//        return 0;
//
//    Function *F = Module_Ob->getFunction(std::string("unary") + Opcode);
//    if (F == 0)
//        return 0;
//
//    return Builder.CreateCall(F, OperandV, "unop");
//}

//for循环的结构的生成
Value *ExprForAST::Codegen() {
    
    //生成start条件的中间代码生成
    Value *StartVal = Start->Codegen();
    
    if (StartVal == 0)
        return 0;
    //获得函数实体
    Function *TheFunction = Builder.GetInsertBlock()->getParent();
    //获得插入的点
    BasicBlock *PreheaderBB = Builder.GetInsertBlock();
    //这里就是将loop:给插入到TheFunction当中
    BasicBlock *LoopBB =
    BasicBlock::Create(MyGlobalContext, "loop", TheFunction);
    
    //然后去创建br指令跳转也就是直接是在entry下面的br label %loop指令
    Builder.CreateBr(LoopBB);
    
    
    
    //设置插入点为loop块
    Builder.SetInsertPoint(LoopBB);
    
    //创建phi节点
    PHINode *Variable = Builder.CreatePHI(Type::getInt32Ty(MyGlobalContext),
                                          2, Var_Name.c_str());
    
    //生成phi节点可以从两个基本块当中得到变量i的两个值
    //其中一个是%entry块表示在循环初始化的时候对i的赋值是1
    //而%loop块对i的值进行更新，完成循环的一次迭代
    /*
     %i = phi i32 [ 1, %entry ], [ %nextvar, %loop ]
     */
    //preheaderBB块代表是entry块
    Variable->addIncoming(StartVal, PreheaderBB);
    
    //根据Var_Name也就是i获取旧的值
    Value *OldVal = Named_Values[Var_Name];
    //然后将新的值给穿进去也就是Variable其实就是PHInode节点
    Named_Values[Var_Name] = Variable;
    
    //然后判断函数体生成是否失败，失败就返回0
    if (Body->Codegen() == 0)
        return 0;
    
    //然后去判断步长
    Value *StepVal;
    if (Step) {
        
        //如果步长存在就直接去调用IR代码生成的函数
        StepVal = Step->Codegen();
        if (StepVal == 0)
            return 0;
    } else {
        //步长不存在就去使用默认的步长
        StepVal = ConstantInt::get(Type::getInt32Ty(MyGlobalContext), 1);
    }
    //创建一个加法指令
    Value *NextVar = Builder.CreateAdd(Variable, StepVal, "nextvar");
    
    //结束代码的生成
    Value *EndCond = End->Codegen();
    if (EndCond == 0)
        return EndCond;
    //创建一个比较指令
    EndCond = Builder.CreateICmpNE(
                                   EndCond, ConstantInt::get(Type::getInt32Ty(MyGlobalContext), 0), "loopcond");
    //获取插入点
    BasicBlock *LoopEndBB = Builder.GetInsertBlock();
    
    //插入到函数当中
    BasicBlock *AfterBB =
    BasicBlock::Create(MyGlobalContext, "afterloop", TheFunction);
    
    //创建跳转指令
    Builder.CreateCondBr(EndCond, LoopBB, AfterBB);
    
    //设置插入点，之后的插入就都在这个afterloop块里面的
    Builder.SetInsertPoint(AfterBB);
    
    //再去设置phi节点的另外一个label，其实就是loop块，LoopEndBB代表的就是loop块
    Variable->addIncoming(NextVar, LoopEndBB);
    
    //旧的值存在的就再去重新设置为1
    if (OldVal)
        Named_Values[Var_Name] = OldVal;
    
    else
        //删除这个节点像上面这样只是删除单个节点
        Named_Values.erase(Var_Name);
    
    return Constant::getNullValue(Type::getInt32Ty(MyGlobalContext));
}
//封装的函数
static void HandleTopExpression() {
    if(FunctionDefnAST *F = top_level_parser()) {
        if(Function *LF = F->Codegen()) {
            TheExecutionEngine->finalizeObject();
            void *FPtr = TheExecutionEngine->getPointerToFunction(LF);
            
            double (*FP)() = (double (*)())(intptr_t)FPtr;
            fprintf(stderr, "Evaluated to %f\n", FP());
        }
    }
    else {
        next_token();
    }
}

//Driver函数由主函数调用，这里的主要做的就是判断文件结束和分号以及def和处理二元表达式
static void Driver(){
    while (1) {
        switch (Current_token) {
            case EOF_TOKEN:return;
            case ';':next_token();break;
            case DEF_TOKEN:HandleDefn();break;
            default:HandleTopExpression(); break;
        }
    }
}
//TOY编译器会以读模式打开Example文件，并且按单词组织成token流，如果遇到了Def关键字就会返回DEF_TOKEN，然后去调用HandleDefn()函数，它会存储函数名和参数，程序会递归地去检查token的类型，然后调用特定的token处理函数，把信息存储在各自的AST当中
int main(int argc, char* argv[]) {
    
    //InitializeNativeTarget——主程序应该调用此函数来初始化与主机对应的本机目标。这对于JIT应用程序非常有用，以确保目标被正确地链接。客户端对这个函数进行多次调用是合法的。
    InitializeNativeTarget();
    //主程序应该调用此函数来初始化本机目标asm打印机
    InitializeNativeTargetAsmPrinter();
    //InitializeNativeTargetAsmParser——主程序应该调用这个函数来初始化本机目标asm解析器。
    InitializeNativeTargetAsmParser();
    
        LLVMContext *llvmcx;
        //LLVMContext针对每一个线程记录了线程本地的变量，即对于每一个LLVM的线程，都对应了这样一个context的实例。
        //管理LLVM核心基础设施的核心“全局”数据，包括类型和常数唯一表
        //该类在多线程的上下文环境中变得非常重要，您可能想为每个线程创建一个本地上下文环境，并且想让每个线程完全独立于其他上下文环境运行。目前，使用这个默认的全局上下文来处理 LLVM 所提供的代码
        llvmcx = &MyGlobalContext;
        
        init_precedence();
    
        file = fopen(argv[1], "r");
        if(file == 0) {
            printf("Could not open file\n");
            return 0;
        }
        //获取Current_token
        next_token();
        //一个Module的实例用于存储一个模块中的所有信息，是其他所有LLVM中间表示对象的容器。每个目标会直接包含一个全局变量的列表，
        //一个函数的列表，和这个模块依赖的函数库的列表，一个符号表，和这个目标特性的一些数据。
        //https://blog.csdn.net/michael_kang/article/details/5976653
        /*
         LLVM 模块类是其他所有 LLVM IR 对象的顶级容器。LLVM 模块类能够包含全局变量、函数、该模块所依赖的其他模块和符号表等对象的列表。这里将提供了 LLVM 模块的构造函数：
         */
    
        Module_Ob = new Module("my compiler", *llvmcx);
    
    std::unique_ptr<Module> Owner = make_unique<Module>("my compiler", *llvmcx);
    Module_Ob = Owner.get();
    

    
    
    std::string ErrStr;
    TheExecutionEngine =
    EngineBuilder(std::move(Owner))
    .setErrorStr(&ErrStr)
    .setMCJITMemoryManager(llvm::make_unique<SectionMemoryManager>())
    .create();
    if (!TheExecutionEngine) {
        exit(1);
    }
        //为Module对象定义一个函数Pass管理器
        legacy::FunctionPassManager My_FP(Module_Ob);
        //增加优化的Pass
         My_FP.add(createCostModelAnalysisPass());
         My_FP.add(createInstructionCombiningPass());
         My_FP.add(createReassociatePass());
         My_FP.add(createNewGVNPass());
         My_FP.add(createCFGSimplificationPass());
         //运行Passes的所有初始化器
          My_FP.doInitialization();
        //之后我们再把一系列的Pass赋值给全局静态函数Pass管理器
        Global_FP = & My_FP;
    
        //驱动程序
        Driver();
    
        Global_FP = 0;
        //dump函数会被调用以输出生成的IR
    
        Module_Ob->dump();
        //Module_Ob->print(dbgs(), nullptr,false,true);
        //Module_Ob->print(llvm::errs(), nullptr);
        return 0;
    
    
    }



