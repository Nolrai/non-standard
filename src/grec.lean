
class has_definedness (α : Type) (β : out_param Type) [preorder β]:= 
  (definedness : α → β)

open has_definedness

infix `.≤`:60 := λ x y, definedness x ≤ definedness y 

