import data.finmap
import .hitchhike

inductive vonNeumann
  | N
  | E
  | S
  | W

def vonNeumann.to_fin4 : vonNeumann → fin 4

def vonNeumann_fin4 : vonNeumann ≃ fin 4 :=
  { to_fun := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _ }

def vonNeumann.cmp (x y : vonNeumann) : ordering :=
  match x, y with
  | vonNeumann.N, vonNeumann.N := ordering.eq
  | vonNeumann.N, _ := ordering.lt
  | vonNeumann.E, vonNeumann.N := ordering.gt
  | vonNeumann.E, vonNeumann.E := ordering.eq
  | vonNeumann.E, _ := ordering.lt
  | vonNeumann.S, vonNeumann.S := ordering.eq
  | vonNeumann.S, vonNeumann.W := ordering.lt
  | vonNeumann.S, _ := ordering.gt
  | vonNeumann.W, vonNeumann.W := ordering.eq
  | vonNeumann.W, _ := ordering.gt
  end

lemma list.mem_pair {α} {x y z : α} {p : Prop} : x ∈ [y, z] → (x = y → p) → (x = z → p) → p :=
  by {
    intros x_y_z x_y x_z, 
    cases x_y_z, 
    apply x_y x_y_z, 
    cases x_y_z, 
    apply x_z x_y_z,
    cases x_y_z,
  }

instance : preorder vonNeumann := 
  {
    le := λ x y, x.cmp y ∈ [ordering.eq, ordering.lt],
    le_refl := by {intros, unfold has_le.le, cases a; left; unfold vonNeumann.cmp},
    le_trans := 
    by {
      intros a b c, 
      unfold has_le.le, 
      intros a_b b_c,
      apply list.mem_pair a_b; clear a_b; intros a_b,
      {
        cases a; cases b; cases a_b; exact b_c,
      },
      right; left,
      apply list.mem_pair b_c; clear b_c; intros b_c,
      {
        cases b; cases c; cases b_c; exact a_b,
      },
      cases a; cases b; cases a_b; cases c; cases b_c; trivial,
    }
  }


lemma vonNeumann_linear_order_aux (a b : vonNeumann) : (a.cmp b).compares a b := 
  by {
    cases a; cases b; unfold vonNeumann.cmp; unfold ordering.compares; 
    unfold has_lt.lt gt; unfold_projs; unfold vonNeumann.cmp,
    all_goals {
      split,
      {right, left, refl},
      intros h, cases h; cases h; cases h,
    },
  }

instance : linear_order vonNeumann := 
  linear_order_of_compares vonNeumann.cmp vonNeumann_linear_order_aux

inductive Moore
  | N
  | NE
  | E
  | SE
  | S
  | SW
  | W
  | NW

class neighborhood (α : Type) :=
  (size : nat)
  (to_ix : α ≃ fin size)
  (rotate_one : α → α)
  (reflect : α → α)

def vonNeumann.rotate_one : vonNeumann → vonNeumann
  | vonNeumann.N := vonNeumann.E
  | vonNeumann.E := vonNeumann.S
  | vonNeumann.S := vonNeumann.W
  | vonNeumann.W := vonNeumann.N

def vonNeumann.reflect : vonNeumann → vonNeumann
  | vonNeumann.E := vonNeumann.W
  | vonNeumann.W := vonNeumann.E
  | x := x

instance : neighborhood vonNeumann := 
  {
    rotate_one := vonNeumann.rotate_one, 
    reflect := vonNeumann.reflect
  }

def Moore.rotate_one : Moore → Moore
  | Moore.N := Moore.NE
  | Moore.NE := Moore.E
  | Moore.E := Moore.SE
  | Moore.SE := Moore.S
  | Moore.S := Moore.SW
  | Moore.SW := Moore.W
  | Moore.W := Moore.NW
  | Moore.NW := Moore.N


def Moore.reflect : Moore → Moore
  | Moore.NE := Moore.NW
  | Moore.NW := Moore.NE
  | Moore.E := Moore.W
  | Moore.W := Moore.E
  | Moore.SE := Moore.SW
  | Moore.SW := Moore.SE
  | x := x

inductive symmetries
  | none
  | rotate2
  | rotate4
  | rotate8
  | rotate4reflect
  | rotate8reflect
  | reflect
  | permute

structure var_line :=
  (name : string)
  (values : finset nat)

inductive value (n : nat)
  | lit : fin n → value
  | var : string → value

structure transition (nh : Type) (n : nat) : Type := 
  (orig : value n)
  (neighboorhood : nh → (value n))
  (new : value n)

infix `~>`:40 := λ α β, finmap (λ _ : α, β)

structure rule_table :=
  (n_states : nat)
  (nh : Type)
  (symmetries: symmetries)
  (vars : string ~> (fin n_states))
  (transitions : rbtree (transition nh n_states))

