module types

type rules // binding

  Var(x) : t
  where definition of x : t
  
  Param(x, t) : t
  
  Fun(p, e) : FunType(t_p, t_e)
  where p : t_p and e : t_e 

  Fix(p, e) : t_p
  where p : t_p and e : t_e and t_p == t_e
        
  App(e1, e2) : t_r
  where e1 : FunType(t_f, t_r) and e2 : t_a
    and t_f == t_a
        else error "type mismatch" on e2
    
  Let(x, t_x, e1, e2) : t2
  where e2 : t2 and e1 : t1 
    and t1 == t_x
        else error "type mismatch" on e1

type rules // arithmetic 
    
  Num(i) : IntType()

  Ifz(e1, e2, e3) : t2
  where e1 : IntType() and e2 : t2 and e3 : t3
    and t2 == t3 
        else error "types not compatible" on e3
  
  e@Add(e1, e2) 
  + e@Sub(e1, e2) 
  + e@Mul(e1, e2) : IntType()
  where e1 : IntType() 
        else error "Int type expected" on e
    and e2 : IntType()
        else error "Int type expected" on e
