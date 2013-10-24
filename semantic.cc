/* ===== semantic.c ===== */
#include <string>
#include <iostream>
#include <map>
#include <list>
#include <vector>


using namespace std;

#include <stdio.h>
#include <stdlib.h>
#include "ptype.hh"
#include "symtab.hh"

#include "myASTnode.hh"



#include "semantic.hh"

// feedback the main program with our error status
int TypeError = 0;


/// ---------- Error reporting routines --------------

void errornumparam(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": The number of parameters in the call do not match."<<endl;
}

void errorincompatibleparam(int l,int n) {
  TypeError = 1;
  cout<<"L. "<<l<<": Parameter "<<n<<" with incompatible types."<<endl;
}

void errorreferenceableparam(int l,int n) {
  TypeError = 1;
  cout<<"L. "<<l<<": Parameter "<<n<<" is expected to be referenceable but it is not."<<endl;
}

void errordeclaredident(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Identifier "<<s<<" already declared."<<endl;
}

void errornondeclaredident(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Identifier "<<s<<" is undeclared."<<endl;
}

void errornonreferenceableleft(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Left expression of assignment is not referenceable."<<endl;
}

void errorincompatibleassignment(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Assignment with incompatible types."<<endl;
}

void errorbooleanrequired(int l,string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Instruction "<<s<<" requires a boolean condition."<<endl;
}

void errorisnotprocedure(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator ( must be applied to a procedure in an instruction."<<endl;
}

void errorisnotfunction(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator ( must be applied to a function in an expression."<<endl;
}

void errorincompatibleoperator(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator "<<s<<" with incompatible types."<<endl;
}

void errorincompatiblereturn(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Return with incompatible type."<<endl;
}

void errorreadwriterequirebasic(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Basic type required in "<<s<<"."<<endl;
}

void errornonreferenceableexpression(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Referenceable expression required in "<<s<<"."<<endl;
}

void errornonfielddefined(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Field "<<s<<" is not defined in the struct."<<endl;
}

void errorfielddefined(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Field "<<s<<" already defined in the struct."<<endl;
}

/// ------------------------------------------------------------
/// Table to store information about program identifiers
symtab symboltable;

static void InsertintoST(int line,string kind,string id,ptype tp)
{
  infosym p;

  if (symboltable.find(id) && symboltable.jumped_scopes(id)==0) errordeclaredident(line,id);
  else {
    symboltable.createsymbol(id);
    symboltable[id].kind=kind;
    symboltable[id].tp=tp;
  }
}

/// ------------------------------------------------------------

bool isbasickind(string kind) {
  return kind=="int" || kind=="bool";
}



void check_params(AST *a,ptype tp,int line,int numparam)
{
  //...
if (!tp && !a){
return;
}
	else if( (tp && !a) || (a &&!tp)){
	errornumparam(line);
	}else if((!(a->right) && tp->right) || (!(tp->right) && a->right)){
		errornumparam(line);
		return;
   	}
else{
   TypeCheck(a);
	   
	   if(tp->kind == "parref" && a->ref == 0){
		errorreferenceableparam(line, numparam + 1);
	   }
	   if(a->tp->kind != "error" && !equivalent_types(tp->down, a->tp)){
		errorincompatibleparam(line, numparam + 1);
	   }
   	check_params(a->right, tp->right, line, numparam+1);
}
}

void insert_vars(AST *a)
{
  if (!a) return;
  TypeCheck(child(a,0));
  InsertintoST(a->line,"idvarlocal",a->text,child(a,0)->tp);
  a->ref=1;
  insert_vars(a->right); 
}

void construct_struct(AST *a)
{
  AST *a1=child(a,0);
  a->tp=create_type("struct",0,0);

  while (a1!=0) {
    TypeCheck(child(a1,0));
    if (a->tp->struct_field.find(a1->text)==a->tp->struct_field.end()) {
      a->tp->struct_field[a1->text]=child(a1,0)->tp;
      a->tp->ids.push_back(a1->text);
     } else {
      errorfielddefined(a1->line,a1->text);
    }
    a1=a1->right;
  }
}

void create_header(AST *a)
{
  /*a = procedure/function*/
  AST *params =child(child(child(a,0),0),0);
  ttypenode *tipus = 0;
  ttypenode *pars = 0;
  ttypenode *actual = 0;
  string tmp;
  int set = 0;
  while(params){
	TypeCheck(child(params,1));
        if(params->kind=="val"){
		tmp = "parval";
	}else{
		tmp = "parref";
	}
	if(set){
		actual->right = create_type(tmp, child(params,1)->tp, 0);
		actual = actual->right;
	}else{
		actual = create_type(tmp, child(params,1)->tp, 0); 
		pars = actual;
		set = 1;
	}
	params = params->right;
  }
  if(a->kind=="procedure"){
	tmp = "idproc";
	tipus = 0;
  }else{
	tmp = "idfunc";
	TypeCheck(child(child(a,0),1));
	tipus = child(child(a,0),1)->tp;;
  }
  ttypenode *func = create_type(a->kind, pars, tipus);
  InsertintoST(a->line,tmp,child(a,0)->text,func);

}


void insert_header(AST *a)
{
  //...
}

void insert_headers(AST *a)
{
  while (a!=0) {
    create_header(a);
    a=a->right;
  }
}


void TypeCheck(AST *a,string info)
{

/*
program
list
procedure && function
"("
ref val
ident
struct
:=
intconst
true &&false
<,>
=
"-" unario
+-/*
and, OR
NOT
isbasickind
writeln
write
"."
while
if
"["
array
String
read
*/
  if (!a) {
    return;
  }

  //cout<<"Starting with node \""<<a->kind<<"\""<<endl;
  if (a->kind=="program") {
    a->sc=symboltable.push();
    insert_vars(child(child(a,0),0)); // d d
    insert_headers(child(child(a,1),0)); //d r d
    TypeCheck(child(a,1),"phunctions");
    TypeCheck(child(a,2),"instr");

    symboltable.pop();
  } 
  else if (a->kind=="list") {
    // At this point only instruction, procedures or parameters lists are possible.
    for (AST *a1=a->down;a1!=0;a1=a1->right) {
      TypeCheck(a1,info);
    }
  } 
else if (a->kind=="procedure"||a->kind=="function"){

      a->sc=symboltable.push();

      TypeCheck(child(child(a,0),0)); //d d
      insert_vars(child(child(a,1),0)); //drd

      insert_headers(child(child(a,2),0));//drrd
      TypeCheck(child(a,2), "phunctions");
      TypeCheck(child(a,3), "instr");
      
      if(a->kind=="function"){
	TypeCheck(child(a,4));

	if(!equivalent_types(child(a,4)->tp, symboltable[child(a,0)->text].tp->right)){
		errorincompatiblereturn(child(a,4)->line);
	}
      }
      symboltable.pop();
  }

else if (a->kind=="("){
      if (!symboltable.find(child(a,0)->text)){
         errornondeclaredident(a->line, child(a,0)->text);
      }else{
	
	if(symboltable[child(a,0)->text].tp->kind != "function" && info!="instr"){
		errorisnotfunction(a->line);
		a->tp = create_type("error", 0, 0);
	}else if(symboltable[child(a,0)->text].tp->kind != "procedure" && info=="instr"){
		errorisnotprocedure(a->line);
		a->tp = create_type("error", 0, 0);
	}
	if(symboltable[child(a,0)->text].tp->kind == "function" || symboltable[child(a,0)->text].tp->kind == "procedure"){
		if(symboltable[child(a,0)->text].tp->kind == "function"){
			a->tp = symboltable[child(a,0)->text].tp->right;
		
		}
		
		check_params(child(child(a,1),0), symboltable[child(a,0)->text].tp->down, a->line, 0);
	}
      }
  } 
  else if (a->kind=="val" || a->kind =="ref"){
    TypeCheck(child(a,1));
    if(a->kind=="ref"){ InsertintoST(a->line,"idparref",child(a,0)->text,child(a,1)->tp);}	
    else{
     InsertintoST(a->line,"idparval",child(a,0)->text,child(a,1)->tp);}
    a->tp=child(a,1)->tp;
}
  else if (a->kind=="ident") {
    if (!symboltable.find(a->text)) {
      errornondeclaredident(a->line, a->text);
      a->tp=create_type("error",0,0);
    } 
    else {
      a->tp=symboltable[a->text].tp;
      a->ref=(a->tp->kind!="procedure" && a->tp->kind!="function");
    }
  } 
  else if (a->kind=="struct") {
    construct_struct(a);
  }
  else if (a->kind==":=") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
  // cout << "el valor de ref es : " << child(a,0)->ref << "\n" ;
    if (child(a,0)->ref == 0) {
      errornonreferenceableleft(a->line,child(a,0)->text);
    }
    else if (child(a,0)->tp->kind!="error" && child(a,1)->tp->kind!="error" &&
	     !equivalent_types(child(a,0)->tp,child(a,1)->tp)) {
      errorincompatibleassignment(a->line);
    } 
    else {
      a->tp=child(a,0)->tp;
    }
  } 
  else if (a->kind=="intconst") {
    a->tp=create_type("int",0,0);
  } 
  else if ( (a->kind=="true" )||( a->kind=="false")){
    a->tp=create_type("bool",0,0);
  }
   else if (a->kind=="<" || a->kind==">"){
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if( (child(a,0)->tp->kind!="int" || child(a,1)->tp->kind!="int") 
	&& child(a,0)->tp->kind!="error" && child(a,1)->tp->kind!="error"){
	errorincompatibleoperator(a->line, a->kind);
    }
    a->tp = create_type("bool", 0, 0);
  } 
   else if(a->kind=="="){
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if(child(a,0)->tp->kind != child(a,1)->tp->kind || !isbasickind(child(a,1)->tp->kind)){
        errorincompatibleoperator(a->line, a->kind);
    }
    a->tp = create_type("bool", 0, 0);
  }
   else if (a->kind=="-" && !(child(a,1))){
	TypeCheck(child(a,0));
	if(child(a,0)->tp->kind == "int"){
	   a->tp = child(a,0)->tp;
	}else{
	   errorincompatibleoperator(a->line,a->kind);
	}
  }

  else if (a->kind=="+" || (a->kind=="-" && child(a,1)!=0) || a->kind=="*"
	   || a->kind=="/") {
    TypeCheck(child(a,0));
    TypeCheck(child(a,1));
    if ((child(a,0)->tp->kind!="error" && child(a,0)->tp->kind!="int") ||
	(child(a,1)->tp->kind!="error" && child(a,1)->tp->kind!="int")) {
      errorincompatibleoperator(a->line,a->kind);
    }
    a->tp=create_type("int",0,0);
  }
 else if(a->kind=="or" || a->kind=="and"){
	TypeCheck(child(a,0));
	TypeCheck(child(a,1));
    if(child(a,0)->tp->kind!="bool" || child(a,1)->tp->kind!="bool"){
	errorincompatibleoperator(a->line, a->kind);
    }
    a->tp = create_type("bool", 0, 0);
  } 
 else if(a->kind=="not") {
    TypeCheck(child(a,0));
    if(child(a,0)->tp->kind!="bool"){
	errorincompatibleoperator(a->line, a->kind);
    }
    a->tp = create_type("bool", 0, 0);
  }
  else if (isbasickind(a->kind)) {
    a->tp=create_type(a->kind,0,0);
  }
  else if (a->kind=="writeln" || a->kind=="write") {
    TypeCheck(child(a,0));
    if (child(a,0)->tp->kind!="error" && !isbasickind(child(a,0)->tp->kind) && child(a,0)->tp->kind!="string") {
      errorreadwriterequirebasic(a->line,a->kind);
    }
  }

  else if (a->kind==".") {
    TypeCheck(child(a,0));
    a->ref=child(a,0)->ref;
    if (child(a,0)->tp->kind!="error") {
      if (child(a,0)->tp->kind!="struct") {
	errorincompatibleoperator(a->line,"struct.");
      }
      else if (child(a,0)->tp->struct_field.find(child(a,1)->text)==
	       child(a,0)->tp->struct_field.end()) {
	errornonfielddefined(a->line,child(a,1)->text);
      } 
      else {
	a->tp=child(a,0)->tp->struct_field[child(a,1)->text];
      }
    }
   else{
    a->ref=0;
   }
  } 
  else if(a->kind=="while"){
  TypeCheck(child(a,0));
    if(child(a,0)->tp->kind!="bool"){
	errorbooleanrequired(a->line,a->kind);
   }
   TypeCheck(child(a,1),"instr");
   
  }
  else if(a->kind=="if"){
   TypeCheck(child(a,0));
   if(child(a,0)->tp->kind!="bool"){
	errorbooleanrequired(a->line,a->kind);
    }
  TypeCheck(child(a,1),"instr");
  TypeCheck(child(a,2),"instr");
  }
  else if (a->kind=="["){
  TypeCheck(child(a,0));
  TypeCheck(child(a,1));
  if(child(a,0)->tp->kind!="array" && child(a,0)->tp->kind!="error"){
  //comprobamos que sea un array
      errorincompatibleoperator(a->line,"array[]");
      if(child(a,1)->tp->kind!="int" && child(a,1)->tp->kind!="error") {
	errorincompatibleoperator(a->line,"[]");
       }
     }else{
	//sabemos que es un array. miramos indices...
	if(child(a,1)->tp->kind !="int" && child(a,1)->tp->kind!="error"){
	errorincompatibleoperator(a->line,"[]");
	}
	if(child(a,0)->tp->kind!="error") {
	  a->tp=child(a,0)->tp->down;
	}
     }
    a->ref=child(a,0)->ref;
  }
  else if(a->kind=="array"){
   TypeCheck(child(a,0));
   if(child(a,0)->tp->kind!="int"){
     errorincompatibleoperator(a->line, "array[]");
   }
   TypeCheck(child(a,1));
   a->tp=create_type(a->kind,0,0);
   a->tp->down = child(a,1)->tp;
   a->tp->numelemsarray=atoi(child(a,0)->text.data());
  }
  else if (a->kind=="string"){
   a->tp=create_type(a->kind,0,0);
  }
  else if (a->kind=="read"){
   TypeCheck(child(a,0));
   if(child(a,0)->ref == 0){
    errornonreferenceableexpression(a->line,a->kind);
   }
   else if (!isbasickind(child(a,0)->tp->kind) && child(a,0)->tp->kind!="error"){
    errorreadwriterequirebasic(a->line,a->kind);
   }

  }

  else {
    cout<<"BIG PROBLEM! No case defined for kind "<<a->kind<<endl;
  }

  //cout<<"Ending with node \""<<a->kind<<"\""<<endl;
}
