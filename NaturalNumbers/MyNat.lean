inductive MyNat: Type where 
  | zero : MyNat 
  | succ : MyNat → MyNat

inductive AExp: Type where 
  | num: ℤ → AExp
