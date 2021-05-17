import data.equiv.basic
import data.equiv.list
import data.equiv.fin

universe u

inductive vonNeumann
  | N
  | E
  | S
  | W

open vonNeumann

def vonNeumann.to_fin4 (dir : vonNeumann) : fin 4 :=
  match dir with
  | N := 0
  | E := 1
  | S := 2
  | W := 3
  end

def fin.to_vonNeumann  : fin 4 → vonNeumann
  | ⟨0, _⟩ := N
  | ⟨1, _⟩ := E 
  | ⟨2, _⟩ := S
  | ⟨3, _⟩ := W
  | ⟨n+4, p⟩ := false.rec vonNeumann (not_le.mpr p ((4 : ℕ).le_add_left n))

lemma vonNeumann.aux (x : fin 4) : x.to_vonNeumann.to_fin4 = x :=
  match x with
  | ⟨0, _⟩ := rfl
  | ⟨1, _⟩ := rfl 
  | ⟨2, _⟩ := rfl
  | ⟨3, _⟩ := rfl
  | ⟨n+4, p⟩ := false.rec _ (not_le.mpr p ((4 : ℕ).le_add_left n))
  end

def vonNeumann_fin4 : vonNeumann ≃ fin 4 :=
{ 
  to_fun := vonNeumann.to_fin4,
  inv_fun := fin.to_vonNeumann,
  left_inv := λ x, by {cases x; unfold vonNeumann.to_fin4; refl},
  right_inv := λ x, by {apply vonNeumann.aux}
}

example {α β} (eqi : α ≃ β) : α ↪ β := equiv.to_embedding eqi

instance : fintype vonNeumann := 
  { 
    elems := (fintype.elems (fin 4)).map vonNeumann_fin4.symm.to_embedding,
    complete := λ nv, finset.mem_map_equiv.mpr (fintype.complete _)
  }

prefix `¡`:50 := equiv.perm

class neighborhood (α : Type) :=
  (size : nat)
  (to_ix' : α ≃ fin size)
  ( rotate_clockwise : ¡α)
  (reflect : ¡α)

def to_ix {α} [neighborhood α] : α ≃ fin (neighborhood.size α) := neighborhood.to_ix'

def vonNeumann.rotate_clockwise' : vonNeumann → vonNeumann
  | N := E
  | E := S
  | S := W
  | W := N

def vonNeumann.rotate_positive' : vonNeumann → vonNeumann
  | N := W
  | E := N
  | S := E
  | W := S

def vonNeumann.reflect' : vonNeumann → vonNeumann
  | E := W
  | W := E
  | x := x

instance : neighborhood vonNeumann := 
  {
    size := 4,
    to_ix' := vonNeumann_fin4,
    rotate_clockwise := 
     { 
      to_fun := vonNeumann.rotate_clockwise',
      inv_fun := vonNeumann.rotate_positive',
      left_inv := by {intro x, cases x; unfold vonNeumann.rotate_clockwise' vonNeumann.rotate_positive'},
      right_inv := by {intro x, cases x; unfold vonNeumann.rotate_clockwise' vonNeumann.rotate_positive'},
     }, 
    reflect := 
    { 
      to_fun := vonNeumann.reflect',
      inv_fun := vonNeumann.reflect',
      left_inv := by {intro x, cases x; unfold vonNeumann.reflect'},
      right_inv := by {intro x, cases x; unfold vonNeumann.reflect'},
     }
  }

def rotate_clockwise {α} [neighborhood α] : α ≃ α := neighborhood.rotate_clockwise
def reflect_nh {α} [neighborhood α] : α ≃ α := neighborhood.reflect

def linear_order.preimage {α β : Type} (f : α ↪ β) [lo : linear_order β] : linear_order α :=
{
  le := λ x y, f x ≤ f y,

  le_refl := λ x, linear_order.le_refl (f x),

  le_antisymm := λ (x y : α) x_y y_x, function.embedding.injective f (linear_order.le_antisymm (f x) (f y) x_y y_x),

  le_trans := λ (x y z : α), linear_order.le_trans (f x) (f y) (f z),

  le_total := λ (a b : α), linear_order.le_total (f a) (f b),

  decidable_le := λ a b, if h : f a ≤ f b then is_true h else is_false h
}

inductive inside_outside : Type
  | inside 
  | outside

open inside_outside

instance : decidable_eq inside_outside 
  | inside inside := is_true rfl
  | outside outside := is_true rfl
  | inside outside := is_false (by {apply inside_outside.no_confusion})
  | outside inside := is_false (by {apply inside_outside.no_confusion})


def inside_outside.to_bool : inside_outside ≃ bool := {
  to_fun := (= inside),
  inv_fun := λ b, if b then inside else outside,
  left_inv := by {
    intros io,
    cases io,
    simp,
    simp,
  },

  right_inv := fun b, by {
    cases b; simp,
  }
}

def inside_outside.to_fin2 : inside_outside ≃ fin 2 :=
  equiv.trans inside_outside.to_bool fin_two_equiv.symm

open vonNeumann

def equiv.on_prod {α α' β β'} (f : α ≃ α') (g : β ≃ β') : (α × β) ≃ (α' × β') := 
{
  to_fun := λ p, ⟨f p.1, g p.2⟩,
  inv_fun := λ p, ⟨f.inv_fun p.1, g.inv_fun p.2⟩,
  left_inv := by {
    intros p,
    obtain ⟨a, b⟩ := p,
    simp only,
    obtain ⟨f,f_inv,f_left,f_right⟩ := f,
    obtain ⟨g,g_inv,g_left,g_right⟩ := g,
    simp only,
    simp_rw equiv.coe_fn_mk,
    congr, {apply f_left}, {apply g_left}
  },

  right_inv := by {
    intros p,
    obtain ⟨a, b⟩ := p,
    simp only,
    obtain ⟨f,f_inv,f_left,f_right⟩ := f,
    obtain ⟨g,g_inv,g_left,g_right⟩ := g,
    simp only,
    simp_rw equiv.coe_fn_mk,
    congr, {apply f_right}, {apply g_right}
  },

}

structure xcell (α : Type u) := (to_array : array 4 α)

def xcell.read {α} (c : xcell α) (dir : vonNeumann) : α := c.to_array.read (vonNeumann_fin4 dir)
def xcell.write {α} (c : xcell α) (dir : vonNeumann) (a : α) : xcell α := 
  ⟨c.to_array.write (vonNeumann_fin4 dir) a⟩

@[ext]
lemma xcell.ext {α} (a b : xcell α) : (∀ vn, a.read vn = b.read vn) ↔ a = b :=
by {
  split,
  {
    intros hyp,
    obtain ⟨a⟩ := a, obtain ⟨b⟩ := b,
    congr,
    ext,
    transitivity ({xcell . to_array := a}.read (vonNeumann_fin4.inv_fun i)),
      {unfold xcell.read, simp},
      {rw hyp, unfold xcell.read, simp}
  },
  {
    intros hyp,
    simp_rw hyp,
    intros vn,
    refl,
  },
}

def template.read_aux : (inside_outside × vonNeumann) ≃ fin 8 := 
  equiv.trans (equiv.on_prod inside_outside.to_fin2 vonNeumann_fin4) fin_prod_fin_equiv

structure template (α : Type) := (to_array : array (8) α)

def template.read_fun {α} (arr : template α) (io : inside_outside) (dir : vonNeumann) : α :=
  arr.to_array.read (template.read_aux (io, dir))

def template.read_inv {α} (f : inside_outside → vonNeumann → α) : template α :=
  ⟨⟨λ ix, function.uncurry f (template.read_aux.inv_fun ix)⟩⟩

lemma equiv.coe_coe_symm {α β} (π : α ≃ β) (b : β) : π (π.symm b) = b :=
by {
  cases π,
  simp,
  rw π_right_inv,
}

lemma equiv.coe_symm_coe {α β} (π : α ≃ β) (a : α) : π.symm (π a) = a :=
by {
  cases π,
  simp,
  rw π_left_inv,
}

def template.read {α} : template α ≃ (inside_outside → vonNeumann → α) :=
{ 
  to_fun := template.read_fun,
  inv_fun := template.read_inv,
  left_inv := λ x,
  by {
    obtain ⟨⟨f⟩⟩ := x,
    unfold template.read_fun template.read_inv,
    congr,
    funext,
    unfold function.uncurry template.read_fun,
    simp,
    unfold array.read d_array.read,
  },
  right_inv := λ f,
  by {
    funext,
    unfold template.read_fun template.read_inv,
    simp only [equiv.inv_fun_as_coe],
    unfold array.read d_array.read,
    simp only,
    have : ((template.read_aux.symm) (template.read_aux (io, dir))) = (io, dir) := equiv.coe_coe_symm _ _,
    rw this,
    rw function.uncurry,
  }
}

def rule (α) := (template α → template α → Prop)

structure board (n m : ℕ) (α : Type u) : Type u := 
  mk :: (to_array : array n (array m (xcell α)))

def board.read {n m} {α} (mat : board n m α) (p : fin n × fin m) := (mat.to_array.read p.1).read p.2

@[simp]
lemma board.read.def {n m : ℕ} {α : Type u} (mat : board n m α) (ix : fin n) (iy : fin m) :
  mat.read ⟨ix, iy⟩ = (mat.to_array.read ix).read iy := rfl

open vonNeumann

def vonNeumann.to_index {n m} : vonNeumann → fin (n+1) × fin (m+1)
  | N := (0, -1)
  | E := (1, 0)
  | S := (0, 1)
  | W := (-1, 0)

def vonNeumann.neg : vonNeumann → vonNeumann
  | N := S
  | E := W
  | S := N
  | W := E

instance : has_neg vonNeumann := ⟨vonNeumann.neg⟩

lemma vonNeumann.neg_involution (dir : vonNeumann) : -(-dir) = dir := 
  match dir with
  | N := rfl
  | E := rfl
  | S := rfl
  | W := rfl
  end

def read_template.aux {n m} {α : Type} 
  (mat : board (n+1) (m+1) α) 
  (ix : fin (n+1) × fin (m+1)) : inside_outside → vonNeumann → α
  | inside dir := (mat.read ix).read dir
  | outside dir := 
    let offset : (fin (n+1) × fin (m+1)) := dir.to_index in
    (mat.read (ix.1 + offset.1, ix.2 + offset.2)).read (-dir)

def read_template {n m} {α : Type} 
  (mat : board (n+1) (m+1) α)
  (ix : fin (n+1) × fin (m+1)) :
  template α := template.read.symm (read_template.aux mat ix)

instance : functor template := { 
  map := λ α β f t, ⟨f <$> t.to_array⟩,
  map_const := λ α β (f : α) t, ⟨f <$ t.to_array⟩
}

lemma template.map.def {α β} {f : α → β} {t : template α} : f <$> t = template.mk (f <$> t.to_array) := rfl

lemma template.comp_map (α β γ : Type)
  (f : α → β)
  (g : β → γ)
  (t : array 8 α) :
  (g ∘ f) <$> t = g <$> f <$> t := by {
  simp only, 
  apply is_lawful_functor.comp_map
}

instance : is_lawful_functor template := {
  id_map := λ α ⟨t⟩, by {have := id_map t, rw template.map.def, simp only, apply this},
  comp_map := λ α β γ f g ⟨t⟩, by {have := comp_map f g t, simp_rw template.map.def, apply this},
}

def template.seq {α β : Type} : template (α → β) → template α → template β
  | f x := template.mk (⟨λ ix, f.to_array.read ix $ x.to_array.read ix⟩)

instance : applicative template := {
  seq := λ _ _, template.seq ,
  pure := λ α a, ⟨⟨λ _, a⟩⟩,
}

def vonNeumann.decidable_eq.aux {α} [decidable_eq α] (f g : vonNeumann → α) : decidable (∀ x, f x = g x) :=
  if h : f N = g N ∧ f E = g E ∧ f S = g S ∧ f W = g W
    then is_true (by {rcases h with ⟨h_n, h_e, h_s, h_w⟩, intros x, cases x; assumption})
    else is_false (λ all, h (by {simp_rw all, repeat {split; try {refl}}}))

instance {α} [decidable_eq α] : decidable_eq (xcell α) :=
  by {
    intros a b,
    rw ← xcell.ext,
    apply vonNeumann.decidable_eq.aux,
  }

def array.to_template (arr : array 8 (fin 2)) : template bool := ⟨arr.map (λ n, if n = 0 then tt else ff)⟩
def array.last {α n} (arr : array (n+1) α) := arr.read (fin.last n)

@[simp]
lemma array.last_def {α n} (arr : array (n+1) α) : arr.last = arr.read (fin.last n) := rfl

instance {α} [linear_order α] : linear_order (template α) := 
  linear_order.preimage (by {
    refine function.embedding.trans ⟨template.to_array, _⟩ ⟨array.to_list, _⟩; intros x y,
    {
      cases x; cases y,
      simp only,
      intro h; exact h,
    },
    {
      intro inj_hyp,
      transitivity x.to_list.to_array,
      have H := (array.to_list_to_array x).symm,
      apply H.elim, refl,
      have H := (array.to_list_to_array y),
      apply H.elim,
      congr' 1,
    }
  })
  
def array.rev {α} {n} (arr : array (n+1) α) : array (n+1) α := ⟨λ ix, arr.read (fin.last n - ix)⟩

notation `#[` arr:(foldr `,` (h t, array.push_back t h) array.nil `]`) := arr.rev

def array.to_vector {n α} (arr : array n α) : vector α n := 
  ⟨arr.to_list, array.to_list_length arr⟩ 

def array.to_templates ( arr : array 2 (array 8 (fin 2))) : (template bool × template bool) :=
  match (arr.map array.to_template).to_vector with
  | ⟨[old, new], _⟩ := ⟨old, new⟩
  end

abbreviation ACA_rules.from_list (rule_list : list (array 2 (array 8 (fin 2)))) (lhs rhs : template bool) : Prop := 
  (lhs, rhs) ∈ (rule_list.map array.to_templates)

instance : ∀ (rules : list _), decidable_rel (ACA_rules.from_list rules)
  | [] lhs rhs := is_false (by {apply list.not_mem_nil})
  | (x::xs) lhs rhs :=
    if h : (lhs, rhs) = x.to_templates
      then is_true (or.inl h)
      else match ACA_rules.from_list.decidable_rel xs lhs rhs with
        | is_true ih := is_true (or.inr ih)
        | is_false ih := is_false (λ hyp, or.dcases_on hyp h ih)
        end

def convert_from_dixons : array 8 (fin 2) → array 8 (fin 2)
  | arr := 
    match arr.to_vector with
    | ⟨[i_top, i_bottom, i_left, i_right, o_top, o_bottom, o_left, o_right], p⟩ := -- T, B, L, R order
      #[i_top, i_right, i_bottom, i_left, o_top, o_right, o_bottom, o_left] -- N, E, S, W order!
    end

def array.from_dixons (arr : array 8 (fin 2)) : template bool := ⟨(convert_from_dixons arr).map fin_two_equiv⟩

inductive LAR
  | L --left
  | A -- Across
  | R -- Right

open LAR

inductive WB
  | E -- Empty
  | F -- Full
open WB

instance : decidable_eq WB
  | E E := is_true rfl
  | F F := is_true rfl
  | E F := is_false (by {apply WB.no_confusion})
  | F E := is_false (by {apply WB.no_confusion})

inductive bcell -- a two cell 
  | EE -- empty
  | FF -- full
  | HH -- half empty : 
  -- out cell on source (head)
  -- in cell on target (co-head) (a cohead is a head in the overlapping template)
open bcell

instance : decidable_eq bcell :=
  by {
    intros x y,
    cases x; cases y; try {exact is_true rfl}; apply is_false; apply bcell.no_confusion
  }

instance : has_coe WB bcell :=
  has_coe.mk $ λ wb,
    match wb with
    | E := EE
    | F := FF
    end

def vonNeumann.move (vn : vonNeumann) : LAR → vonNeumann 
  | L := rotate_clockwise (rotate_clockwise (rotate_clockwise vn))
  | A := rotate_clockwise (rotate_clockwise vn)
  | R := rotate_clockwise vn

structure lhs_template :=
  (head : vonNeumann)
  (at_L : WB)
  (at_A : WB)
  (at_R : WB)

structure rhs_template :=
  (old_head : WB)
  (at_L : bcell)
  (at_A : bcell)
  (at_R : bcell)

open lhs_template
open rhs_template

instance : has_coe_to_fun lhs_template :=
  {
    F := λ _, LAR → WB,
    coe := λ t lar,
    match lar with
    | L := lhs_template.at_L t
    | A := lhs_template.at_A t 
    | R := lhs_template.at_R t
    end
  }

instance : has_coe_to_fun rhs_template :=
  {
    F := λ _, LAR → bcell,
    coe := λ (t : rhs_template) lar,
    match lar with
    | L := rhs_template.at_L t
    | A := rhs_template.at_A t 
    | R := rhs_template.at_R t
    end
  }

inductive LHZ_base : lhs_template → rhs_template → Prop
| move_forward          : ∀ nv, LHZ_base ⟨nv, E, E, E⟩ ⟨E, EE, HH, EE⟩
| turn_left_head_on     : ∀ nv, LHZ_base ⟨nv, E, F, E⟩ ⟨E, EE, FF, HH⟩
| turn_right            : ∀ nv, LHZ_base ⟨nv, E, E, F⟩ ⟨E, HH, EE, FF⟩
| toggle_memory         : ∀ nv, LHZ_base ⟨nv, F, F, E⟩ ⟨F, EE, HH, FF⟩

def lhs_template.to_template (lhs : lhs_template) : template bool :=
  let rotate : vonNeumann → vonNeumann :=
    match head lhs with -- is used contravalently So is "backwards"
    | N := λ vn, vn.move R
    | E := λ vn, vn.move A
    | S := λ vn, vn.move L
    | W := id
    end in
  let as_fun (io : inside_outside) (vn : vonNeumann) : bool :=
    match vn with
    | N := ite (lhs.at_L = F) tt ff
    | E := ite (lhs.at_A = F) tt ff
    | S := ite (lhs.at_R = F) tt ff
    | W := ite (io = outside) tt ff
    end in
  template.read.inv_fun (λ io nv, as_fun io (rotate nv))

def on_bcell : bcell → inside_outside → bool
| FF _ := tt
| EE _ := ff
| HH io := if io = inside then tt else ff

def rhs_template.to_template (rhs : rhs_template) (lhs_head : vonNeumann) : template bool :=
  let rotate : vonNeumann → vonNeumann :=
    match lhs_head with -- is used contravalently So is "backwards"
    | N := λ vn, vn.move R
    | E := λ vn, vn.move A
    | S := λ vn, vn.move L
    | W := id
    end in
  let as_fun (io : inside_outside) (vn : vonNeumann) : bool :=
    match vn with
    | N := on_bcell rhs.at_L io
    | E := on_bcell rhs.at_A io
    | S := on_bcell rhs.at_R io 
    | W := to_bool (rhs.old_head = F)
    end in
  template.read.inv_fun (λ io nv, as_fun io (rotate nv))

def template.print {α} (to_char : α → char) (t : template α) : string := 
  match t.to_array.to_vector with
  | ⟨[i_north, i_east, i_south, i_west, o_north, o_east, o_south, o_west], _⟩ :=
    "\n  " ++ ⟨[to_char o_north]⟩ ++ "  \n" ++
    "  " ++ ⟨[to_char i_north]⟩ ++ "  \n" ++
    ⟨[to_char o_west, to_char i_west, ' ', to_char i_east, to_char o_east]⟩ ++ "\n" ++
    "  " ++ ⟨[to_char i_south]⟩ ++ "  \n" ++
    "  " ++ ⟨[to_char o_south]⟩ ++ "  \n"
  end

instance : has_to_string (template bool) := ⟨template.print (λ b, if b then '╬' else '█')⟩

def board.write {n m : ℕ} {α} (mat : board n m α) (pos : fin n × fin m) (a : xcell α) : board n m α :=
  ⟨mat.to_array.write pos.1 ((mat.to_array.read pos.1).write pos.2 a)⟩

def write_template.aux {n m} {α : Type} 
  (mat : board (n+1) (m+1) α) 
  (ix : fin (n+1) × fin (m+1)) : inside_outside → vonNeumann → α → board (n+1) (m+1) α
  | inside  dir a := let old := (mat.read ix) in mat.write ix (old.write dir a) 
  | outside dir a := 
    let offset : (fin (n+1) × fin (m+1)) := dir.to_index in
    let ix' := (ix.1 + offset.1, ix.2 + offset.2) in
    let old := (mat.read ix') in
    mat.write ix (old.write (-dir) a)

def write_template {n m : ℕ} {α : Type} 
  (M : board (n+1) (m+1) α) (ix : fin (n+1) × fin (m+1)) (t : template α) :
  board (n+1) (m+1) α :=
  let action_list : list (board (n+1) (m+1) α → board (n+1) (m+1) α) :=
    do
    i_o <- [inside, outside],
    dir <- [N, E, S, W],
    pure (λ m : board (n+1) (m+1) α, write_template.aux m ix i_o dir (template.read t i_o dir)) in
  action_list.foldl (λ m f, f m) M

example : ∀ n m : ℕ, n ≤ n + m := nat.le_add_right
example : ∀ n m : ℕ, n ≤ m → ¬ m < n := λ _ _, not_lt_of_le

inductive step {α} [linear_order α] (rules : template α → template α → Prop) {n m : ℕ} : 
  board (n+1) (m+1) α → board (n+1) (m+1) α → Prop
  | intro : ∀ (p : fin (n+1) × fin (m+1)) (mat : board (n+1) (m+1) α) (b),
    rules (read_template mat p) b → step mat (write_template mat p b)

abbreviation is_head {n m} (mat : board (n+1) (m+1) bool) (pos : fin (n+1) × fin (m+1)) : Prop :=
  ∃ b, LHZ (read_template mat pos) b 

theorem LHZ_preserves_heads (n m : ℕ) (m₁ m₂ : board (n+3) (m+3) bool) (h : step LHZ m₁ m₂) :
  {p // is_head m₁ p} ≃ {p // is_head m₂ p} := 
{
  to_fun := λ ⟨p, ⟨b, p_h⟩⟩, _,
  inv_fun := _,
  left_inv := _,
  right_inv := _ 
}