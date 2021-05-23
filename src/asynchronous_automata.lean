import data.equiv.basic
import data.equiv.list
import data.equiv.fin
import data.finmap
import order.lexicographic

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

@[ext]
lemma template.ext {α} (x y : template α) : x.read = y.read → x = y :=
by {
  intro hyp,
  exact template.read.apply_eq_iff_eq.mp hyp
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

def vonNeumann.move : LAR → vonNeumann ≃ vonNeumann 
  | L := rotate_clockwise.trans (rotate_clockwise.trans rotate_clockwise)
  | A := rotate_clockwise.trans rotate_clockwise
  | R := rotate_clockwise

instance : decidable_eq vonNeumann := equiv.decidable_eq vonNeumann_fin4

structure lhs_template_body :=
  (at_L : WB)
  (at_A : WB)
  (at_R : WB)

structure lhs_template :=
  (head : vonNeumann)
  (body : lhs_template_body)

structure rhs_template :=
  (old_head : WB)
  (at_L : bcell)
  (at_A : bcell)
  (at_R : bcell)

open lhs_template
open rhs_template

instance : decidable_eq lhs_template 
  | ⟨vn, l, a, r⟩ ⟨vn', l', a', r'⟩ :=
    if h : vn = vn' ∧ l = l' ∧ a = a' ∧ r = r'
      then is_true (by {obtain ⟨vn_h, l_h, a_h, r_h⟩ := h, congr; assumption})
      else is_false (by {intros target, injection target, injection h_2, apply h, repeat {split}; assumption})

instance : decidable_eq rhs_template 
  | ⟨wb, l, a, r⟩ ⟨wb', l', a', r'⟩ :=
    if h : wb = wb' ∧ l = l' ∧ a = a' ∧ r = r'
      then is_true (by {obtain ⟨vn_h, l_h, a_h, r_h⟩ := h, congr; assumption})
      else is_false (by {intros target, injection target, apply h, repeat {split}; assumption})

instance : has_coe_to_fun lhs_template :=
  {
    F := λ _, LAR → WB,
    coe := λ t lar,
    match lar with
    | L := lhs_template_body.at_L (lhs_template.body t)
    | A := lhs_template_body.at_A (lhs_template.body t)
    | R := lhs_template_body.at_R (lhs_template.body t)
    end
  }

@[simp]
lemma lhs_at_L (lhs : lhs_template) : lhs L = lhs.body.at_L := rfl 
@[simp]
lemma lhs_at_A (lhs : lhs_template) : lhs A = lhs.body.at_A := rfl 
@[simp]
lemma lhs_at_R (lhs : lhs_template) : lhs R = lhs.body.at_R := rfl 

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

@[simp]
lemma rhs_at_L (rhs : rhs_template) : rhs L = at_L rhs := rfl 
@[simp]
lemma rhs_at_A (rhs : rhs_template) : rhs A = at_A rhs := rfl 
@[simp]
lemma rhs_at_R (rhs : rhs_template) : rhs R = at_R rhs := rfl

inductive LHZ_base : lhs_template -> rhs_template -> Type
| move_forward          : ∀ nv, LHZ_base ⟨nv, E, E, E⟩ ⟨E, EE, HH, EE⟩
| turn_left_head_on     : ∀ nv, LHZ_base ⟨nv, E, F, E⟩ ⟨E, EE, FF, HH⟩
| turn_right            : ∀ nv, LHZ_base ⟨nv, E, E, F⟩ ⟨E, HH, EE, FF⟩
| toggle_memory         : ∀ nv, LHZ_base ⟨nv, F, F, E⟩ ⟨F, EE, HH, FF⟩

def rotate_with_head (lhs_head : vonNeumann) : vonNeumann ≃ vonNeumann :=
  match lhs_head with 
  | N := vonNeumann.move L
  | E := vonNeumann.move A
  | S := vonNeumann.move R
  | W := equiv.refl vonNeumann
  end

namespace lhs_template

def aux₂ (lhsb : lhs_template_body) (io : inside_outside) (vn : vonNeumann) : bool:= 
  match vn with
  | N := ite (lhsb.at_L = F) tt ff
  | E := ite (lhsb.at_A = F) tt ff
  | S := ite (lhsb.at_R = F) tt ff
  | W := ite (io = outside) tt ff
  end

end lhs_template

instance : linear_order inside_outside := 
  linear_order.lift inside_outside.to_fin2 inside_outside.to_fin2.injective

instance : fintype inside_outside := 
  fintype.of_equiv (fin 2) inside_outside.to_fin2.symm

def inside_outside.repr : inside_outside → string
  | inside := "inside" 
  | outside := "inside"

def vonNeumann.repr : vonNeumann → string
| N := "N"
| E := "E"
| S := "S"
| W := "W"

instance : has_repr inside_outside := ⟨inside_outside.repr⟩
instance : has_repr vonNeumann := ⟨vonNeumann.repr⟩

namespace lhs_template

def in_order := [(inside, N), (inside, E), (inside, S), (inside, W), (inside, N), (inside, E), (inside, S), (inside, W)]

open function

lemma aux₂_injective : function.injective aux₂ :=
by {
  intros x y h,
  have : in_order.map (uncurry (aux₂ x)) = in_order.map (uncurry (aux₂ y)) := by {rw h},
  clear h, rename this h,
  cases x; cases x_at_L; cases x_at_A; cases x_at_R;
    cases y; cases y_at_L; cases y_at_A; cases y_at_R,
  all_goals {
    try {refl},
  },
  all_goals {
    unfold in_order at h,
    simp_rw [list.map_cons, list.map_nil, function.uncurry_def] at h,
    unfold aux₂ at h,
    simp at h,
    cases h,
  }
}

def to_template (lhs : lhs_template) : template bool :=
  template.read.inv_fun (λ io vn, aux₂ lhs.body io (rotate_with_head (lhs.head) vn))

def is_head (f : inside_outside → bool) : Prop := 
  f inside = ff ∧ f outside = tt 

lemma head_at_head.aux (lhsb : lhs_template_body) (vn : vonNeumann) : is_head (λ io, aux₂ lhsb io vn) ↔ vn = W :=
by {
  unfold is_head,
  cases vn,
  case W {
    apply iff_of_true _ rfl,
    funext,
    unfold aux₂,
    split,
    apply if_neg, {intros h, cases h},
    apply if_pos, {refl}
  },
  all_goals {
    apply iff_of_false _,
    {
      intro h,
      cases h,
    },
    intros crazy,
    obtain ⟨inside_crazy, outside_crazy⟩ := crazy,
    have : ff = tt,
    unfold aux₂ at *,
    transitivity ite (_ = F) tt ff,
    symmetry,
    exact inside_crazy,
    exact outside_crazy,
    cases this,
  },
}

def is_head_at (t : template bool) (vn : vonNeumann) : Prop := 
  is_head (λ io, template.read t io vn)

lemma head_at_head (lhs : lhs_template) : 
  is_head_at (lhs.to_template) lhs.head :=
by {
  cases lhs; cases lhs_head,
  all_goals {
      unfold lhs_template.to_template is_head_at,
      simp,
      rw head_at_head.aux,
      unfold rotate_with_head,
      try {unfold vonNeumann.move,
        try {simp_rw equiv.coe_trans},
        unfold rotate_clockwise,
        unfold_projs,
        rw ← equiv.to_fun_as_coe,
        simp only [function.comp_app],
        unfold rotate_clockwise'
      },
  },
  {
    rw equiv.coe_refl,
    rw id,
  }
}

lemma not_head_at_not_head (lhs : lhs_template) (vn : vonNeumann)  (vn_neq_lhs_head : vn ≠ lhs.head) : 
  ¬ is_head_at (lhs.to_template) vn :=
  match lhs, vn, vn_neq_lhs_head with
  | {head := N, body := _}, N, p := 
    λ _ , false.rec false (p (eq.refl N))
  | {head := E, body := _}, E, p := 
    λ _ , false.rec false (p (eq.refl E))
  | {head := S, body := _}, S, p := 
    λ _ , false.rec false (p (eq.refl S))
  | {head := W, body := _}, W, p := 
    λ _ , false.rec false (p (eq.refl W))
  
  -- head := N
  | {head := N, body := _}, E, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := N, body := _}, S, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := N, body := _}, W, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  
  -- head := E
  | {head := E, body := _}, N, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := E, body := _}, S, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := E, body := _}, W, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }

    -- head := S
  | {head := S, body := _}, N, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := S, body := _}, E, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := S, body := _}, W, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }

  -- head := W
  | {head := W, body := _}, N, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := W, body := _}, E, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  | {head := W, body := _}, S, p := 
    by {
      unfold is_head_at lhs_template.to_template,
      simp,
      unfold rotate_with_head,
      try {
        unfold vonNeumann.move,
        unfold_coes,
        unfold rotate_clockwise,
        unfold_projs,
        unfold vonNeumann.rotate_clockwise'
      },
      rw head_at_head.aux,
      apply vonNeumann.no_confusion,
    }
  end

lemma iff_head_at_head (lhs : lhs_template) (vn : vonNeumann) :
  (vn = lhs.head) ↔ is_head_at lhs.to_template vn :=
by {
  split; intros h,
  {rw h, exact head_at_head lhs},
  {contrapose h, exact not_head_at_not_head lhs vn h}
}

lemma to_template_injective : function.injective lhs_template.to_template :=
  by {
    intros x y h,
    have x_head_eq_y_head : x.head = y.head,
    rw iff_head_at_head,
    rw ← h,
    exact head_at_head x,
    cases x; cases y; simp at *,
    rw x_head_eq_y_head at *, clear x_head_eq_y_head x_head,
    split, {refl},
    unfold lhs_template.to_template at h, simp at h,
    set f := rotate_with_head y_head,
    have : aux₂ x_body = aux₂ y_body,
    funext,
    have : ∃ vn', vn = f vn' := ⟨f.inv_fun vn, _⟩,
    obtain ⟨vn', vn_eq ⟩ := this,
    rw vn_eq,
    transitivity (λ (io : inside_outside) (vn : vonNeumann), aux₂ x_body io (f vn)) io vn',
    {simp},
    {rw h},
    rw ← equiv.to_fun_as_coe,
    rw f.right_inv,
    apply aux₂_injective this,
  }

end lhs_template

def on_bcell : bcell → inside_outside → bool
| FF _ := tt
| EE _ := ff
| HH io := if io = inside then tt else ff

def rhs_template.to_template (rhs : rhs_template) (lhs_head : vonNeumann) : template bool :=
  let as_fun (io : inside_outside) (vn : vonNeumann) : bool :=
    match vn with
    | N := on_bcell rhs.at_L io
    | E := on_bcell rhs.at_A io
    | S := on_bcell rhs.at_R io 
    | W := to_bool (rhs.old_head = F)
    end in
  template.read.inv_fun (λ io nv, as_fun io (rotate_with_head lhs_head nv))

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

lemma LHZ_base.unique (l r) (a b : LHZ_base l r) : a = b :=
  by {cases a; cases b; refl}

def LHZ_any := Σ' l r, ∃ x : LHZ_base l r, true

instance : decidable_eq LHZ_any 
  | ⟨a_l, a_r, a_h⟩ ⟨b_l, b_r, b_h⟩ :=
  if h : a_l = b_l
  then is_true 
    (by {
      obtain ⟨a_h, _x⟩ := a_h, cases _x,
      obtain ⟨b_h, _x⟩ := b_h, cases _x,
      cases a_h; cases b_h; cases h; refl,
    })
  else is_false
    (by {
      intros target,
      injection target,
      exact h h_1,
    })

def vn_to_LHZ (vn : vonNeumann) : list LHZ_any :=
  [ ⟨_, _, LHZ_base.move_forward vn, true.intro⟩
  , ⟨_, _, LHZ_base.turn_left_head_on vn, true.intro⟩
  , ⟨_, _, LHZ_base.turn_right vn, true.intro⟩
  , ⟨_, _, LHZ_base.toggle_memory vn, true.intro⟩
  ]

lemma vn_to_LHZ.complete  (l r) (x : LHZ_base l r) : 
  (⟨l,r,x,true.intro⟩ : LHZ_any) ∈ vn_to_LHZ (l.head):= 
by {
  unfold vn_to_LHZ,
  cases x; cases x_1; simp,
}

def LHZ.elems := ([N, E, S, W].bind vn_to_LHZ)

lemma LHZ.elems.complete : ∀ (x : LHZ_any), x ∈ LHZ.elems
  | ⟨l, r, x, true.intro⟩ := by {
    unfold LHZ.elems; unfold list.bind; unfold list.map,
    rw list.mem_join,
    cases x with vn vn vn vn,
    all_goals 
      {
        cases vn, 
        case N {use vn_to_LHZ N, simp, apply vn_to_LHZ.complete},
        case E {use vn_to_LHZ E, simp, apply vn_to_LHZ.complete},
        case S {use vn_to_LHZ S, simp, apply vn_to_LHZ.complete},
        case W {use vn_to_LHZ W, simp, apply vn_to_LHZ.complete},
    }
  }

instance : fintype LHZ_any := 
{ 
  elems := LHZ.elems.to_finset,
    
  complete := LHZ.elems.complete
}

inductive LHZ : template bool → template bool → Prop
  | mk : ∀ lhs rhs, LHZ_base lhs rhs → LHZ (lhs.to_template) (rhs.to_template (head lhs))

infixr ` ~> ` :40 := λ α β, finmap (λ _ : α, β)

def LHZ_any.to_pair : LHZ_any → (Σ _:lhs_template, rhs_template)
  | ⟨l, r, _⟩ := ⟨l, r⟩

def LHZ_base.finmap : lhs_template ~> rhs_template := 
  (LHZ.elems.map LHZ_any.to_pair).to_finmap

lemma list.map_nodup {α β : Type u} 
  (f : α → β) (f_inj : function.injective f) 
  (l : list α) :
  l.nodup ↔ (l.map f).nodup :=
by {
  unfold list.nodup,
  induction l,
  {rw list.map_nil, exact iff_of_true list.pairwise.nil list.pairwise.nil},
  {
    rw list.map_cons,
    simp_rw list.pairwise_cons,
    have : ∀ (a b c d : Prop), (b ↔ d) → (a ↔ c) → (a ∧ b ↔ c ∧ d), 
    { 
      clear_except,
      intros a b c d b_d a_c,
      split; intros h; obtain ⟨x, y⟩ := h,
      {rw [← b_d, ← a_c], split; assumption},
      {rw [b_d, a_c], split; assumption}
    },
    apply this; clear this,
    {exact l_ih},
    split; intros h a a_in crazy; rw ← crazy at a_in; clear crazy,
    {apply h l_hd, rw ← list.mem_map_of_injective f_inj, exact a_in, refl},
    {apply h (f l_hd), rw list.mem_map_of_injective f_inj, exact a_in, refl}
  }
}

section finmap_bimap

variables {α α' : Type u} {β : α → Type u} {β' : α' → Type u}
variables (m : finmap β)
variables (f : (Σ x, β x) → (Σ x, β' x)) 

def list.nodupkeys_map 
  (l : list (Σ x, β x)) (l_nodupkeys : l.nodupkeys) : 
  (∀ (a₁ a₂ : Σ x, β x), (f a₁).1 = (f a₂).1 → a₁.1 = a₂.1) → (l.map f).nodupkeys :=
by {
  intros f_hyp,
  induction l,
  apply list.nodupkeys_nil,
  rw list.map_cons,
  apply list.nodupkeys_cons.mpr,
  rw list.nodupkeys_cons at l_nodupkeys,
  obtain ⟨nodupkeys_hd, nodupkeys_tl⟩ := l_nodupkeys,
  split,
  {
    intro crazy,
    unfold list.keys at crazy,
    simp_rw list.mem_map at crazy,
    obtain ⟨x, ⟨y, y_in_l_tl, f_y_eq_x⟩, crazy⟩ := crazy,
    rw ← f_y_eq_x at *, clear' x f_y_eq_x,
    have : y.fst = l_hd.fst := f_hyp y l_hd crazy,
    rw ← this at nodupkeys_hd,
    rw list.mem_keys at nodupkeys_hd,
    apply nodupkeys_hd,
    use y.snd,
    simp,
    apply y_in_l_tl,
  },
  {exact l_ih nodupkeys_tl},
}

def finmap.bimap (f_hyp : _) 
  : finmap β' := 
  { finmap . 
    entries := m.entries.map f, 
    nodupkeys := by {
      cases m,
      simp,
      induction m_entries,
      simp at *,
      apply @list.nodupkeys_map; try {assumption},
      refl,
    }
  }

end finmap_bimap

def LHZ.finmap.aux : (Σ (x : lhs_template), rhs_template) → (Σ (x : template bool), template bool)
  | ⟨lhs, rhs⟩ := ⟨lhs.to_template, rhs.to_template lhs.head⟩

def LHZ.finmap : template bool ~> template bool := 
  (LHZ_base.finmap).bimap LHZ.finmap.aux (by {
    intros a₁ a₂ h,
    obtain ⟨l₁, r₁⟩ := a₁,
    obtain ⟨l₂, r₂⟩ := a₂,
    unfold LHZ.finmap.aux at h,
    simp at *,
    clear_except h,

  })
  
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

inductive step {α} [linear_order α]  
  {n m : ℕ} (mat : board (n+1) (m+1) α) : 
  (template α → template α → Type) → 
  board (n+1) (m+1) α → Type 2 
  | intro : 
  ∀ (p : fin (n+1) × fin (m+1)) 
    {rules : template α → template α → Type}
    (b : template α)
    (r_a_b : rules (read_template mat p) b),
    step rules (write_template mat p b)

inductive path {α} [linear_order α] (rules : template α → template α → Type) {n m : ℕ} (a : board (n+1) (m+1) α) : 
  board (n+1) (m+1) α → Type 2
  | refl : path a
  | snoc : ∀ {b c} (tail : path b) (head : step b rules c), path c

def path.append {α} [linear_order α] (rules : template α → template α → Type) {n m : ℕ} {a b c : board (n+1) (m+1) α} :
  path rules a b → path rules b c → path rules a c :=
by {
  intros a_b b_c,
  induction b_c, 
  case refl {exact a_b},
  case snoc {apply path.snoc b_c_ih b_c_head},
}

abbreviation is_head {n m} (mat : board (n+1) (m+1) bool)
  (pos : fin (n+1) × fin (m+1)) (vn : vonNeumann):=
  let t := (read_template mat pos).read in
    t outside vn = tt ∧ t inside vn = ff

abbreviation is_true_head {n m} (mat : board (n+1) (m+1) bool) (pos : fin (n+1) × fin (m+1)) : Type :=
  Σ' b, LHZ (read_template mat pos) b

lemma LHZ_base.targets_have_one_cohead : ∀ lhs rhs, LHZ_base lhs rhs -> ∃! dir : LAR, rhs dir = HH :=
  by {
    intros lhs rhs h,
    cases h,
    { 
      use A, 
      split,
      {simp},
      intro y; cases y; simp,
    },
    {
      use R,
      split,
      {simp},
      intro y; cases y; simp,
    },
    {
      use L,
      split,
      {simp},
      intro y; cases y; simp,
    },
    {
      use A,
      split,
      {simp},
      intro y; cases y; simp,
    },
  }
  
