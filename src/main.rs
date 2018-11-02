use std::collections::HashMap;


fn main() {
	
	//enum for untyped terms
	#[derive(Clone)]
	#[derive(Debug)]
	enum UntypedTerm {
		INT{value: u32},
	    BOOL{value: bool},
	    VAR{name: char},
	    FUN{param: char, body: Box<UntypedTerm>},
	    APP{fun: Box<UntypedTerm>, arg: Box<UntypedTerm>},
	    CALC{op: char, exp1: Box<UntypedTerm>, exp2: Box<UntypedTerm>},
	    NOT{exp: Box<UntypedTerm>},
	    AND{exp1: Box<UntypedTerm>, exp2: Box<UntypedTerm>},
	    OR{exp1: Box<UntypedTerm>, exp2: Box<UntypedTerm>},
	    EQU{exp1: Box<UntypedTerm>, exp2: Box<UntypedTerm>},
	    LT{exp1: Box<UntypedTerm>, exp2: Box<UntypedTerm>},
	    IF{exp1: Box<UntypedTerm>, exp2: Box<UntypedTerm>, exp3: Box<UntypedTerm>},
	    LET{exp1: char, exp2: Box<UntypedTerm>, exp3: Box<UntypedTerm>}
	}
	
	//enum for types
	#[derive(Clone)]
	#[derive(Debug)]
	#[derive(PartialEq, Eq, Hash)]
	enum Type {
		TyInt,
		TyBool,
		TyVar{num: u32},
		TyFun{ParamTy: Box<Type>, ReturnTy: Box<Type>}
	}
	
	//generate fresh type variable
	fn freshVar(v: &mut u32) -> Type {
		*v+=1;
		Type::TyVar{num: *v}
	} 
	
	//enum for typed terms
	#[derive(Clone)]
	#[derive(Debug)]
	enum TypedTerm {
		T_INT{ty: Type, value: u32},
	    T_BOOL{ty: Type, value: bool},
	    T_VAR{ty: Type, name: char},
	    T_FUN{ty: Type, param: Box<TypedTerm>, body: Box<TypedTerm>},
	    T_Closure{fun: Box<TypedTerm>, env: InterpEnv},
	    T_APP{ty: Type, fun: Box<TypedTerm>, arg: Box<TypedTerm>},
	    T_CALC{ty: Type, op: char, exp1: Box<TypedTerm>, exp2: Box<TypedTerm>},
	    T_NOT{ty: Type, exp: Box<TypedTerm>},
	    T_AND{ty: Type, exp1: Box<TypedTerm>, exp2: Box<TypedTerm>},
	    T_OR{ty: Type, exp1: Box<TypedTerm>, exp2: Box<TypedTerm>},
	    T_EQU{ty: Type, exp1: Box<TypedTerm>, exp2: Box<TypedTerm>},
	    T_LT{ty: Type, exp1: Box<TypedTerm>, exp2: Box<TypedTerm>},
	    T_IF{ty: Type, exp1: Box<TypedTerm>, exp2: Box<TypedTerm>, exp3: Box<TypedTerm>},
	    T_LET{ty: Type, exp1: Box<TypedTerm>, exp2: Box<TypedTerm>, exp3: Box<TypedTerm>}
	}
	
	
	impl TypedTerm {
		//function for typed term that return its type
		fn getType(self) -> Type {
			match self {
				TypedTerm::T_INT{ty: t, value: v} => t,
			    TypedTerm::T_BOOL{ty: t, value: v} => t,
			    TypedTerm::T_VAR{ty: t, name: n} => t,
			    TypedTerm::T_FUN{ty: t, param: p, body: b} => t,
			    TypedTerm::T_APP{ty: t, fun: f, arg: a} => t,
			    TypedTerm::T_CALC{ty: t, op: o, exp1: e1, exp2: e2} => t,
			    TypedTerm::T_NOT{ty: t, exp: e} => t,
			    TypedTerm::T_AND{ty: t, exp1: e1, exp2: e2} => t,
			    TypedTerm::T_OR{ty: t, exp1: e1, exp2: e2} => t,
			    TypedTerm::T_EQU{ty: t, exp1: e1, exp2: e2} => t,
			    TypedTerm::T_LT{ty: t, exp1: e1, exp2: e2} => t,
			    TypedTerm::T_IF{ty: t, exp1: e1, exp2: e2, exp3: e3} => t,
			    TypedTerm::T_LET{ty: t, exp1: e1, exp2: e2, exp3: e3} => t,
			    _ => panic!("undefined")  
			}
		}
	}
	
	//type environment
	#[derive(Clone)]
	struct TypeEnv {
		Env: HashMap<char,Type>
	}
	
	impl TypeEnv {
		
		//insert (type variable, type) pair into type environment
		fn set(&mut self, name: char, ty: Type) {
			self.Env.insert(name, ty);			
		}
		
		//return type of an existing type variable
		fn get(self, name: char) -> Type {		
			self.Env.get(&name).unwrap().clone()
		} 
	}
	
	//convert untyped terms to typed terms
	//assign a fresh type variable for sub term.
	//A lot of recursion work.
	fn annotate(term: UntypedTerm, mut tenv: TypeEnv, varNum: &mut u32) -> TypedTerm {
		//let mut typeNum = 0;
		match term {
			UntypedTerm::INT{value: val} => TypedTerm::T_INT{ty: freshVar(varNum), value: val},
			UntypedTerm::BOOL{value: b} => TypedTerm::T_BOOL{ty: freshVar(varNum), value: b},
			UntypedTerm::FUN{param: p, body: b} => {
				let paramTy = freshVar(varNum);
				let paramTy1 = paramTy.clone();
				tenv.set(p, paramTy);
				let paramBinder = TypedTerm::T_VAR{ty: paramTy1, name: p};				
				TypedTerm::T_FUN{ty: freshVar(varNum), param: Box::new(paramBinder), body: Box::new(annotate(*b, tenv, varNum))}
			},
			UntypedTerm::VAR{name: n} => {
				match tenv.get(n) {
					Type::TyVar{num: n1} => TypedTerm::T_VAR{ty: Type::TyVar{num: n1}, name: n},
					_ => panic!("unbound identifier")
				}
			},
			UntypedTerm::CALC{op: o, exp1: e1, exp2: e2} => TypedTerm::T_CALC{ty: freshVar(varNum), op: o, exp1: Box::new(annotate(*e1, tenv.clone(), varNum)), exp2: Box::new(annotate(*e2, tenv.clone(), varNum))},
			UntypedTerm::APP{fun: f, arg: a} => TypedTerm::T_APP{ty: freshVar(varNum), fun: Box::new(annotate(*f, tenv.clone(), varNum)), arg: Box::new(annotate(*a, tenv.clone(), varNum))},
			UntypedTerm::NOT{exp: e} => TypedTerm::T_NOT{ty: freshVar(varNum), exp: Box::new(annotate(*e, tenv.clone(), varNum))},
		    UntypedTerm::AND{exp1: e1, exp2: e2} => TypedTerm::T_AND{ty: freshVar(varNum), exp1: Box::new(annotate(*e1, tenv.clone(), varNum)), exp2: Box::new(annotate(*e2, tenv.clone(), varNum))},
		    UntypedTerm::OR{exp1: e1, exp2: e2} => TypedTerm::T_OR{ty: freshVar(varNum), exp1: Box::new(annotate(*e1, tenv.clone(), varNum)), exp2: Box::new(annotate(*e2, tenv.clone(), varNum))},
		    UntypedTerm::EQU{exp1: e1, exp2: e2} => TypedTerm::T_EQU{ty: freshVar(varNum), exp1: Box::new(annotate(*e1, tenv.clone(), varNum)), exp2: Box::new(annotate(*e2, tenv.clone(), varNum))},
		    UntypedTerm::LT{exp1: e1, exp2: e2} => TypedTerm::T_LT{ty: freshVar(varNum), exp1: Box::new(annotate(*e1, tenv.clone(), varNum)), exp2: Box::new(annotate(*e2, tenv.clone(), varNum))},
		    UntypedTerm::IF{exp1: e1, exp2: e2, exp3: e3} => TypedTerm::T_IF{ty: freshVar(varNum), exp1: Box::new(annotate(*e1, tenv.clone(), varNum)), exp2: Box::new(annotate(*e2, tenv.clone(), varNum)), exp3: Box::new(annotate(*e3, tenv.clone(), varNum))},
		    UntypedTerm::LET{exp1: e1, exp2: e2, exp3: e3} => {
		    	let paramTy = freshVar(varNum);
				let paramTy1 = paramTy.clone();
				tenv.set(e1, paramTy);
				let paramBinder = TypedTerm::T_VAR{ty: paramTy1, name: e1};
				TypedTerm::T_LET{ty: freshVar(varNum), exp1: Box::new(paramBinder), exp2: Box::new(annotate(*e2, tenv.clone(), varNum)), exp3: Box::new(annotate(*e3, tenv.clone(), varNum))}
		    },
		    //TypedTerm::T_LET{ty: freshVar(varNum), exp1: Box::new(annotate(*e1, tenv.clone(), varNum)), exp2: Box::new(annotate(*e2, tenv.clone(), varNum)), exp3: Box::new(annotate(*e3, tenv.clone(), varNum))},
			_ => panic!("undefined term!")
		}
	}
	
	//struct for constraint
	#[derive(Clone)]
	#[derive(Debug)]
	struct Constraint {
		typeA: Type,
		typeB: Type
	}
	
	//collect constraints of a typed term into a set
	fn collect(term: TypedTerm) -> Vec<Constraint> {
		match term {
			TypedTerm::T_INT{ty: t, value: v} => vec![Constraint{typeA: t, typeB: Type::TyInt}],
			TypedTerm::T_BOOL{ty: t, value: v} => vec![Constraint{typeA: t, typeB: Type::TyBool}],
			TypedTerm::T_FUN{ty: t, param: p, body: b} => {
				//collect constraints for body recursively
				let mut vec1 = collect(*b.clone());
				//then add a constraint that function's type should be (param type -> body type)
				vec1.push(Constraint{typeA: t, typeB: Type::TyFun{ParamTy: Box::new(p.getType()), ReturnTy: Box::new(b.getType())}});
				vec1
			}
			TypedTerm::T_VAR{ty: t, name: n} => vec![],
			TypedTerm::T_APP{ty: t, fun: f, arg: a} => {
				//collect constraints for fun and arg recursively
				let mut vec1 = collect(*f.clone());
				let mut vec2 = collect(*a.clone());
				vec1.append(&mut vec2);
				//then add a constraint that function's type should be (arg type -> application type)
				vec1.push(Constraint{typeA: f.getType(), typeB: Type::TyFun{ParamTy: Box::new(a.getType()), ReturnTy: Box::new(t)}});
				vec1
			}
			TypedTerm::T_CALC{ty: t, op: o, exp1: e1, exp2: e2} => {
				//collect constraints for exp1 and exp2 recursively
				let mut vec1 = collect(*e1.clone());
				let mut vec2 = collect(*e2.clone());
				vec1.append(&mut vec2);
				//types of exp1, exp2, OP expression should all be Int.
				vec1.push(Constraint{typeA: t.clone(), typeB: e1.getType()});
				vec1.push(Constraint{typeA: t.clone(), typeB: e2.getType()});
				vec1.push(Constraint{typeA: t, typeB: Type::TyInt});
				vec1
			},
			TypedTerm::T_NOT{ty: t, exp: e} => {
				let mut vec1 = collect(*e.clone());
				vec1.push(Constraint{typeA: t.clone(), typeB: e.getType()});
				vec1.push(Constraint{typeA: t, typeB: Type::TyBool});
				vec1
			},
			TypedTerm::T_AND{ty: t, exp1: e1, exp2: e2} => {
				//collect constraints for exp1 and exp2 recursively
				let mut vec1 = collect(*e1.clone());
				let mut vec2 = collect(*e2.clone());
				vec1.append(&mut vec2);
				//types of exp1, exp2, And expression should all be Bool.
				vec1.push(Constraint{typeA: t.clone(), typeB: e1.getType()});
				vec1.push(Constraint{typeA: t.clone(), typeB: e2.getType()});
				vec1.push(Constraint{typeA: t, typeB: Type::TyBool});
				vec1
			},
			TypedTerm::T_OR{ty: t, exp1: e1, exp2: e2} => {
				//collect constraints for exp1 and exp2 recursively
				let mut vec1 = collect(*e1.clone());
				let mut vec2 = collect(*e2.clone());
				vec1.append(&mut vec2);
				//types of exp1, exp2, Or expression should all be Bool.
				vec1.push(Constraint{typeA: t.clone(), typeB: e1.getType()});
				vec1.push(Constraint{typeA: t.clone(), typeB: e2.getType()});
				vec1.push(Constraint{typeA: t, typeB: Type::TyBool});
				vec1
			},
			TypedTerm::T_EQU{ty: t, exp1: e1, exp2: e2} => {
				//collect constraints for exp1 and exp2 recursively
				let mut vec1 = collect(*e1.clone());
				let mut vec2 = collect(*e2.clone());
				vec1.append(&mut vec2);
				//equal expression is bool but exp1&2 can be both Bool or Int.
				vec1.push(Constraint{typeA: e1.getType(), typeB: e2.getType()});
				vec1.push(Constraint{typeA: t.clone(), typeB: Type::TyBool});
				vec1
			},
			TypedTerm::T_LT{ty: t, exp1: e1, exp2: e2} => {
				//collect constraints for exp1 and exp2 recursively
				let mut vec1 = collect(*e1.clone());
				let mut vec2 = collect(*e2.clone());
				vec1.append(&mut vec2);
				//Less than expression returns Bool and exp1&2 must be Int.
				vec1.push(Constraint{typeA: e1.getType(), typeB: Type::TyInt});
				vec1.push(Constraint{typeA: e2.getType(), typeB: Type::TyInt});
				vec1.push(Constraint{typeA: t, typeB: Type::TyBool});
				vec1
			},
			TypedTerm::T_IF{ty: t, exp1: e1, exp2: e2, exp3: e3} => {
				//collect constraints for exp1, exp2 and exp3 recursively
				let mut vec1 = collect(*e1.clone());
				let mut vec2 = collect(*e2.clone());
				let mut vec3 = collect(*e3.clone());
				vec1.append(&mut vec2);
				vec1.append(&mut vec3);
				//types of exp1 must be Bool, If expression returns the same type as exp1&2.
				vec1.push(Constraint{typeA: e2.clone().getType(), typeB: e3.getType()});
				vec1.push(Constraint{typeA: e1.getType(), typeB: Type::TyBool});
				vec1.push(Constraint{typeA: t, typeB: e2.getType()});
				vec1
			},
			TypedTerm::T_LET{ty: t, exp1: e1, exp2: e2, exp3: e3} => {
				//collect constraints for exp1, exp2 and exp3 recursively
				let mut vec1 = collect(*e2.clone());
				let mut vec2 = collect(*e3.clone());
				vec1.append(&mut vec2);
				//types of e1 and e2 must be the same. types of let and ee must be the same.
				vec1.push(Constraint{typeA: e1.getType(), typeB: e2.getType()});
				vec1.push(Constraint{typeA: t, typeB: e3.getType()});
				vec1
			},
			_ => panic!("undefined")
		}
	}
	
	//struct for substitution containing solutions set
	#[derive(Debug)]
	#[derive(Clone)]
	struct Substitution {
		solutions: HashMap<u32 ,Type>
	}
	
	impl Substitution {
		
		//generate an empty substitution
		fn empty() -> Substitution {
			Substitution{solutions: HashMap::new()}
		}
		
		//generate a solution
		fn fromPair(tvar: u32, ty: Type) -> Substitution {
			let mut s1 = HashMap::new();
			s1.insert(tvar, ty);
			Substitution{solutions: s1}
		}
		
		//apply solutions to rest constraints 
		fn applyToSet (&self,constraints: &mut Vec<Constraint>) -> Vec<Constraint> {
			for elem in constraints.iter_mut() {
				//traverse target constraint set and update each type in all elements. 
			    *elem = Constraint{typeA: Self::applyOneType(&self, elem.typeA.clone()), typeB: Self::applyOneType(&self,elem.typeB.clone())}
			}
			constraints.clone()
		}
		
		//do type replacement that update the type according to solution type 
		fn applyOneType(&self, ty: Type) -> Type {
			match ty {
				Type::TyInt => ty,
				Type::TyBool => ty,
				Type::TyFun{ParamTy: p, ReturnTy: r} => Type::TyFun{ParamTy: Box::new(Self::applyOneType(&self, *p)),ReturnTy: Box::new(Self::applyOneType(&self, *r))},
				Type::TyVar{num: n} => {
					let mut t = ty.clone();
					for (key, value) in &self.solutions {
				        if *key == n {t = value.clone()}
				    }
					t
				}
			}
		}

		//update type variables in raw solution based on current solutions and merge solutions into solution sets.   
		fn compose(&mut self, other: Substitution) -> Substitution {
			//update type variables in solution set based on current solution
			for solutionType in self.solutions.values_mut() {
			    *solutionType = Self::applyOneType(&other, solutionType.clone())
			}
			
			//merge current solution into solution sets
			for (key, value) in other.solutions {
		        self.solutions.insert(key, value);
		    }
			Substitution{solutions: self.solutions.clone()}
		}
	}
	
	//Unification
	fn unify(mut constraints: Vec<Constraint>) -> Substitution {
		if constraints.is_empty() {
			Substitution{solutions: HashMap::new()}
		} else {
			
			//unify for the first constraint
			let mut solutionOne = unifyOne(constraints[0].clone());
			//remove the first constraint from constraints set
			let mut vec1 = constraints.split_off(1);
			//update constraints set that replace type variables by the first solution
			let mut updateConstraints = solutionOne.applyToSet(&mut vec1);
			//unify rest constraints
			let solutionRest = unify(updateConstraints);
			//merge current solution into solution sets and update type variables in solution set 
			solutionOne.compose(solutionRest)
		}
	}
	
	//find a solution for one constraint
	fn unifyOne(constraint: Constraint) -> Substitution {
		match (constraint.typeA, constraint.typeB) {
			(Type::TyInt, Type:: TyInt) => Substitution{solutions: HashMap::new()},
			(Type::TyBool, Type:: TyBool) => Substitution{solutions: HashMap::new()},
			(Type::TyFun{ParamTy: p1, ReturnTy: r1}, Type:: TyFun{ParamTy: p2, ReturnTy: r2}) => unify(vec![Constraint{typeA: *p1, typeB: *p2},Constraint{typeA: *r1, typeB: *r2}]),
			(Type::TyVar{num: n}, ty) => unifyVar(n, ty),
			(ty, Type::TyVar{num: n}) => unifyVar(n, ty), 
			(_,_) => panic!("cannot unify")
			
		}
	}
	
	//Unify a constraint containing type variable and another type.
	fn unifyVar(tvar: u32, ty: Type) -> Substitution {
		match ty {
			//do nothing if they are the same type variable
			Type::TyVar{num: n} => {
				if tvar == n {
					Substitution{solutions: HashMap::new()}
				} else {
					//generate a solution if they are different type variable
					let mut s1 = HashMap::new();
					s1.insert(tvar, ty);
					Substitution{solutions: s1}
				}
			},
			
			//if "another type" is not type variable
			ty1 => {
				
				//check if the type variable occurs in "another type"
				if occurs(tvar, ty1.clone()) {
					panic!("Circular use")
				} else {
					//if not, then generate a solution.
					let mut s1 = HashMap::new();
					s1.insert(tvar, ty1);
					Substitution{solutions: s1}
				}
			}
		}
	}
	
	//check if the type variable occurs in "another type"
	fn occurs(tvar: u32, ty: Type) -> bool {
		match ty {
			Type::TyFun{ParamTy: p, ReturnTy: r} => occurs(tvar, *p) || occurs(tvar, *r),
			Type::TyVar{num: n} => tvar == n,
			_ => false
		}
	}
	
	//do type inference
	//if not panic then interp it
	fn typeInference(term: UntypedTerm) {
		let mut EnvT = TypeEnv{Env: HashMap::new()};
	    let TypedTerm = annotate(term, EnvT, &mut 0);
	    let Constraints = collect(TypedTerm.clone());
	    let solutions = unify(Constraints);
	    //println!("Type inference:");
	    println!("Solution set is:");
	    println!("{:?}", solutions);
	    println!(" ");
	    println!("Type of target term is:");
	    println!("{:?}", solutions.applyOneType(TypedTerm.clone().getType()));
	    println!(" ");
	}

	//interp environment
	#[derive(Clone)]
	#[derive(Debug)]
	struct InterpEnv {
		Env: HashMap<char,TypedTerm>
	}
	
	//Env for lambda interpreter
	impl InterpEnv {
		
		//insert (var, value) pair into type environment
		fn set(&mut self, var: char, val: TypedTerm) {
			self.Env.insert(var, val);			
		}
		
		//return value of a var
		fn get(self, var: char) -> TypedTerm {		
			self.Env.get(&var).unwrap().clone()
		} 
	}
	
	//lambda interpreter. The same structure as A2
	fn Interp(term: TypedTerm, env: &mut InterpEnv) -> TypedTerm {
	    match term {
	        TypedTerm::T_INT{ty: t, value: v} => TypedTerm::T_INT{ty: t, value: v},
	        TypedTerm::T_BOOL{ty: t, value: v} => TypedTerm::T_BOOL{ty: t, value: v},
	        TypedTerm::T_VAR{ty: t, name: n} => {
	        	if env.Env.contains_key(&n) {env.clone().get(n)} else {panic!("unknown variable")}
	        },
	        TypedTerm::T_FUN{ty: t, param: p, body: b} => TypedTerm::T_Closure{fun: Box::new(TypedTerm::T_FUN{ty: t, param: p, body: b}), env: env.clone()},
	        TypedTerm::T_APP{ty: t, fun: f, arg: a} => {
	        	let v1 = Interp(*f, env);
	        	let mut EnvNew = InterpEnv{Env: HashMap::new()};
	        	let v2 = Interp(*a, &mut EnvNew);
	        	match v1 {
	        		TypedTerm::T_Closure{fun: f, env: mut e} => match *f.clone() {
	        			TypedTerm::T_FUN{ty: t1, param: p1, body: b1} => match *p1.clone() {
	        				TypedTerm::T_VAR{ty: t2, name: n1} => {
	        					e.set(n1, v2);
	        					Interp(*b1.clone(), &mut e)
	        				},
	        				_ => panic!("undefined")
	        			},
	        			_ => panic!("undefined")
	        		},
	        		_ => panic!("undefined")
	        	}
	        },
	        TypedTerm::T_CALC{ty: t, op: o, exp1: e1, exp2: e2} => {
	        	let v1 = Interp(*e1, env);
	        	let v2 = Interp(*e2, env);
	        	match o {
	        	'+' => Add(v1,v2),
	        	'-' => Minus(v1,v2),
	        	'*' => Mul(v1,v2),
	        	'/' => Div(v1,v2),
	        	_ => panic!("undefined !")
		        }
	        },
	        TypedTerm::T_NOT{ty: t, exp: e} => {
	        	let v1 = Interp(*e, env);
	        	match v1 {
		        	TypedTerm::T_BOOL{ty: t, value: v} => TypedTerm::T_BOOL{ty: t, value: !v},
		        	_ => panic!("undefined !")
	        	}
	        },
	        TypedTerm::T_AND{ty: t, exp1: e1, exp2: e2} => {
	        	let v1 = Interp(*e1, env);
	        	let v2 = Interp(*e2, env);
	        	And(v1, v2)
	        }
	        TypedTerm::T_OR{ty: t, exp1: e1, exp2: e2} => {
	        	let v1 = Interp(*e1, env);
	        	let v2 = Interp(*e2, env);
	        	Or(v1, v2)
	        },
	        TypedTerm::T_EQU{ty: t, exp1: e1, exp2: e2} => {
	        	let v1 = Interp(*e1, env);
	        	let v2 = Interp(*e2, env);
	        	Equ(v1, v2)
	        },
	        TypedTerm::T_LT{ty: t, exp1: e1, exp2: e2} => {
	        	let v1 = Interp(*e1, env);
	        	let v2 = Interp(*e2, env);
	        	Lt(v1, v2)
	        },
	        TypedTerm::T_IF{ty: t, exp1: e1, exp2: e2, exp3: e3} => {
	        	let v1 = Interp(*e1, env);
	        	let v2 = Interp(*e2, env);
	        	let v3 = Interp(*e3, env);
	        	match v1 {
	        		TypedTerm::T_BOOL{ty: t1, value: v} => if v {v2} else {v3},
	        		_ => panic!("undefined !")
	        	}
	        }
	        TypedTerm::T_LET{ty: t, exp1: e1, exp2: e2, exp3: e3} => {
	        	//let v1 = Interp(*e1, env);
	        	let mut EnvNew = InterpEnv{Env: HashMap::new()};
	        	let v2 = Interp(*e2, &mut EnvNew);
	        	match *e1.clone() {
		        	TypedTerm::T_VAR{ty: t, name: n} => {
		        		env.set(n,v2);
			        	Interp(*e3, env)
	        		},
	        		_ => panic!("undefined !")
	        	}	        	
	        }
	        _ => panic!("undefined !")
	    }
	}
	
	fn InterpE(term: UntypedTerm) {
		let mut EnvT = TypeEnv{Env: HashMap::new()};
	    let TypedTerm = annotate(term, EnvT, &mut 0);
	    let Constraints = collect(TypedTerm.clone());
	    let solutions = unify(Constraints);
	    println!("Interpretation result:");
	    let mut EnvI = InterpEnv{Env: HashMap::new()};
	    //println!("Result is:");
	    println!("{:?}",Interp(TypedTerm, &mut EnvI));
	}
	
	//arithmetic operation
	fn Add(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_INT{ty: t1, value: v1}, TypedTerm::T_INT{ty: t2, value: v2}) => TypedTerm::T_INT{ty: Type::TyInt, value: v1+v2},
			_ => panic!("undefined !")
		}
	}
	
	fn Minus(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_INT{ty: t1, value: v1}, TypedTerm::T_INT{ty: t2, value: v2}) => TypedTerm::T_INT{ty: Type::TyInt, value: v1-v2},
			_ => panic!("undefined !")
		}
	}
	
	fn Mul(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_INT{ty: t1, value: v1}, TypedTerm::T_INT{ty: t2, value: v2}) => TypedTerm::T_INT{ty: Type::TyInt, value: v1*v2},
			_ => panic!("undefined !")
		}
	}
	
	fn Div(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_INT{ty: t1, value: v1}, TypedTerm::T_INT{ty: t2, value: v2}) => TypedTerm::T_INT{ty: Type::TyInt, value: v1/v2},
			_ => panic!("undefined !")
		}
	}
	
	fn Lt(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_INT{ty: t1, value: v1}, TypedTerm::T_INT{ty: t2, value: v2}) => TypedTerm::T_BOOL{ty: Type::TyInt, value: v1 < v2},
			_ => panic!("undefined !")
		}
	}
	
	//bool operation
	fn And(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_BOOL{ty: t1, value: v1}, TypedTerm::T_BOOL{ty: t2, value: v2}) => TypedTerm::T_BOOL{ty: Type::TyBool, value: v1 && v2},
			_ => panic!("undefined !")
		}
	}
	
	fn Or(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_BOOL{ty: t1, value: v1}, TypedTerm::T_BOOL{ty: t2, value: v2}) => TypedTerm::T_BOOL{ty: Type::TyBool, value: v1 || v2},
			_ => panic!("undefined !")
		}
	}
	
	fn Equ(a1: TypedTerm, a2: TypedTerm,) -> TypedTerm {
		match (a1,a2) {
			(TypedTerm::T_BOOL{ty: t1, value: v1}, TypedTerm::T_BOOL{ty: t2, value: v2}) => TypedTerm::T_BOOL{ty: Type::TyBool, value: v1 == v2},
			(TypedTerm::T_INT{ty: t1, value: v1}, TypedTerm::T_INT{ty: t2, value: v2}) => TypedTerm::T_BOOL{ty: Type::TyBool, value: v1 == v2},
			_ => panic!("undefined !")
		}
	}
	
	//test cases:
	
	//i1 is int 5
	let i1 = UntypedTerm::INT{value: 5};
	//b1 is bool true
	let b1 = UntypedTerm::BOOL{value: true};
	let c1 = UntypedTerm::CALC{op: '+',exp1: Box::new(UntypedTerm::INT{value: 3}),exp2: Box::new(UntypedTerm::VAR{name: 'x'})};
	let f1 = UntypedTerm::FUN{param: 'x', body: Box::new(c1)};
	let a1 = UntypedTerm::APP{fun: Box::new(f1.clone()), arg: Box::new(i1.clone())};
	
	//c3 is calc x+y
	let c2 = UntypedTerm::CALC{op: '+',exp1: Box::new(UntypedTerm::VAR{name: 'y'}),exp2: Box::new(UntypedTerm::VAR{name: 'x'})};
	//f2 is \x. x+y
	let f2 = UntypedTerm::FUN{param: 'x', body: Box::new(c2)};
	//f3 is \y.\x. x+y
	let f3 = UntypedTerm::FUN{param: 'y', body: Box::new(f2)};
	//a2 is application (\y.\x. x+y) 5
	let a2 = UntypedTerm::APP{fun: Box::new(f3.clone()), arg: Box::new(i1.clone())};
	//a3 is application ((\y.\x. x+y)5)5
	let a3 = UntypedTerm::APP{fun: Box::new(a2.clone()), arg: Box::new(i1.clone())};
	
	let mut EnvT = TypeEnv{Env: HashMap::new()};
	println!("!!!!!!!!!!!!!!!!!!!!!");
	println!("{:?}",annotate(i1.clone(), EnvT, &mut 0));
	
	//typeInference return the whole solution set and type of a term.
	//in this case, f3 is \y.\x. x+y, so type of f3 is "TyFun { ParamTy: TyInt, ReturnTy: TyFun { ParamTy: TyInt, ReturnTy: TyInt } }", which is No.2 in solutions set
	//that means f3 is function takes an int, return a funtion2. Function2 takes an int and returns an int.
	println!("Type inference for \\y.\\x. x+y:");
    typeInference(f3.clone());
    //InterpE do type inference first, if it is well-typed then print return type and do interpretation.
    println!("Interpretation for ((\\y.\\x. x+y)5)5:");
    InterpE(a3);
    
    let e1 = UntypedTerm::EQU{exp1: Box::new(UntypedTerm::VAR{name: 'x'}), exp2: Box::new(i1.clone())};
    let l1 = UntypedTerm::LET{exp1: 'x', exp2: Box::new(i1.clone()), exp3: Box::new(e1.clone())};
    println!(" ");
    println!("Type inference for let x=5 in x==5? :");
    typeInference(l1.clone());
    //InterpE do type inference first, if it is well-typed then print return type and do interpretation.
    println!("Interpretation for let x=5 in x==5?:");
    InterpE(l1);
    
    let f4 = UntypedTerm::FUN{param: 'x', body: Box::new(UntypedTerm::VAR{name: 'x'})};
    println!(" ");
    println!("Type inference for \\x.x :");
    //in this case, f4 is identity function \x. x, so type of f4 is "TyFun { ParamTy: TyVar { num: 1 }, ReturnTy: TyVar { num: 1 } }"
	//that means f4 is function takes a param type t1, returns the same type t1.
    typeInference(f4.clone());
    
    let a4 = UntypedTerm::APP{fun: Box::new(a2.clone()), arg: Box::new(b1.clone())};
    println!(" ");
    println!("Type inference for ((\\y.\\x. x+y)5)true:");
    //in this case, try to apply a bool value to an arithmetic exp.
    //It panic because of "cannot unify"
    typeInference(a4.clone());
    
}
