import data.equiv.basic
import data.equiv.list

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

inductive symmetries
  | none
  | rotate2
  | rotate4
  | rotate4reflect
  | reflect
  | permute

open symmetries

def symmetries.encode : symmetries → ℕ 
  | none              := 0
  | rotate2           := 1
  | rotate4           := 2
  | rotate4reflect    := 4
  | reflect           := 6
  | permute           := 7

def symmetries.decode : ℕ → option symmetries
  | 0 := symmetries.none              
  | 1 := rotate2           
  | 2 := rotate4           
  | 3 := option.none
  | 4 := rotate4reflect    
  | 5 := option.none    
  | 6 := reflect           
  | 7 := permute           
  | (n + 8) := option.none

instance : encodable symmetries :=
  {
    encode := symmetries.encode,
    decode := symmetries.decode,
    encodek := λ a, by {cases a; unfold symmetries.encode symmetries.decode; congr}
  }

def linear_order.preimage {α β : Type} (f : α ↪ β) [lo : linear_order β] : linear_order α :=
{
  le := λ x y, f x ≤ f y,

  le_refl := λ x, linear_order.le_refl (f x),

  le_antisymm := λ (x y : α) x_y y_x, function.embedding.injective f (linear_order.le_antisymm (f x) (f y) x_y y_x),

  le_trans := λ (x y z : α), linear_order.le_trans (f x) (f y) (f z),

  le_total := λ (a b : α), linear_order.le_total (f a) (f b),

  decidable_le := λ a b, if h : f a ≤ f b then is_true h else is_false h
}
instance : linear_order symmetries := linear_order.preimage (encodable.encode' _)

infix `~>`:40 := λ α β, finmap (λ _ : α, β)

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

def template.read_aux : (inside_outside × vonNeumann) ≃ fin 8 := 
  equiv.trans (equiv.on_prod inside_outside.to_fin2 vonNeumann_fin4) fin.prod_equiv

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

def ACA_rule (α) := (template α → template α → Prop)

structure xcell (α : Type) := (to_array : array 4 α)

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

def ACA_board (n m) (α : Type) := aMatrix n m (xcell α) 

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
  (mat : ACA_board (n+1) (m+1) α) 
  (ix : fin (n+1) × fin (m+1)) : inside_outside → vonNeumann → α
  | inside dir := (mat.read ix).read dir
  | outside dir := 
    let offset : (fin (n+1) × fin (m+1)) := dir.to_index in
    (mat.read (ix.1 + offset.1, ix.2 + offset.2)).read (-dir)

def read_template {n m} {α : Type} 
  (mat : ACA_board (n+1) (m+1) α)
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

def bneq {α} [decidable_eq α] (x y : α) :=
  if x ≠ y then tt else ff

def template.hamming {α} [decidable_eq α] (a b: template α) : ℕ :=
  (bneq <$> a <*> b).to_array.count id

def aMatrix.hamming {α n m} [decidable_eq α] (a b: aMatrix n m α) : ℕ :=
  array.count (⟨λ ix, bneq a.flattened b.flattened⟩ : array (n * m) bool) id

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

structure ACA_step {α : Type} [decidable_eq α] (r : ACA_rule α) {n m} (a b : ACA_board (n+1) (m+1) α) :=
   (ix : fin (n+1) × fin (m+1))
   (t₀ t₁ : template α)
   (r_t₀_t₁ : r t₀ t₁)
   (a_matches_t₀ : read_template a ix = t₀)
   (b_matches_t₁ : read_template b ix = t₁)
   (no_other_difference : a.hamming b = t₀.hamming t₁)

inductive path {α : Type} (r : α → α → Type) : α → α → Type
  | refl : ∀ a, path a a
  | snoc : ∀ a b c, path a b → r b c → path a c

def weak_reachabable {α : Type} [decidable_eq α] (r : ACA_rule α) {n m} (a b : ACA_board (n+1) (m+1) α) :=
  inhabited (path (ACA_step r) a b)

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

def ACA_rules.from_list : list (array 2 (array 8 (fin 2))) → template bool ~> template bool
  | l :=
    let to_templates : array 2 (array 8 (fin 2)) → (Σ _, template bool) :=
      λ arr, 
        match (arr.map array.to_template).to_vector with
        | ⟨[old, new], _⟩ := ⟨old, new⟩
        end
      in (l.map to_templates).to_finmap

def convert_from_dixons : array 8 (fin 2) → array 8 (fin 2)
  | arr := 
    match arr.to_vector with
    | ⟨[i_top, i_bottom, i_left, i_right, o_top, o_bottom, o_left, o_right], p⟩ := -- T, B, L, R order
      #[i_top, i_right, i_bottom, i_left, o_top, o_right, o_bottom, o_left] -- N, E, S, W order!
    end

def convert_from_dixons' : array 2 (array 8 (fin 2)) → array 2 (array 8 (fin 2))
  | arr := arr.map convert_from_dixons

def LHZ_list := 
  list.map (λ arr, array.map arr convert_from_dixons)
  [
    #[#[0,0,0,0,0,0,1,0], #[0,0,0,1,0,0,0,0]], -- move forward
    #[#[1,0,0,0,1,1,0,0], #[1,0,0,1,1,0,0,0]], -- Turn Left (head on)
		#[#[0,0,1,0,0,1,1,0], #[0,0,1,1,0,0,1,0]], -- Turn Left (right side collison)
		#[#[1,0,0,1,1,1,0,1], #[1,0,1,1,1,0,0,1]], -- Turn Right
		#[#[0,0,1,1,0,1,1,1], #[1,1,0,1,1,1,0,0]]  -- Toggle Memory
  ]

def LHZ_base : template bool ~> template bool :=
  ACA_rules.from_list LHZ_list

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

def aMatrix.write {n m : ℕ} {α} (M : aMatrix n m α) (ix : fin n × fin m) (a : α) : aMatrix n m α :=
  ⟨M.flattened.write (aMatrix.read.aux ix.1 ix.2) a⟩

def write_template.aux {n m} {α : Type} 
  (mat : aMatrix (n+1) (m+1) (xcell α)) 
  (ix : fin (n+1) × fin (m+1)) : inside_outside → vonNeumann → α → aMatrix (n+1) (m+1) (xcell α)
  | inside  dir a := let old := (mat.read ix) in mat.write ix (old.write dir a) 
  | outside dir a := 
    let offset : (fin (n+1) × fin (m+1)) := dir.to_index in
    let ix' := (ix.1 + offset.1, ix.2 + offset.2) in
    let old := (mat.read ix') in
    mat.write ix (old.write (-dir) a)

def write_template {n m : ℕ} {α : Type} 
  (M : ACA_board (n+1) (m+1) α) (ix : fin (n+1) × fin (m+1)) (t : template α) :
  ACA_board (n+1) (m+1) α :=
  let action_list : list (ACA_board (n+1) (m+1) α → ACA_board (n+1) (m+1) α) :=
    do
    i_o <- [inside, outside],
    dir <- [N, E, S, W],
    pure (λ m : ACA_board (n+1) (m+1) α, write_template.aux m ix i_o dir (template.read t i_o dir)) in
  action_list.foldl (λ m f, f m) M

open equiv

instance : decidable_eq vonNeumann := equiv.decidable_eq vonNeumann_fin4

def vonNeuman_to.linear_order.aux : (vonNeumann → vonNeumann) ↪ list (fin 4) :=
  ⟨λ f, (vonNeumann_fin4 ∘ f : vonNeumann → (fin 4)) <$> [N, E, S, W],
  by {
    intros f g h,
    simp at h,
    rcases h with ⟨h_N, h_E, h_S, h_W⟩,
    funext x, cases x; assumption
  }⟩

instance : linear_order (vonNeumann → vonNeumann) :=
  linear_order.preimage vonNeuman_to.linear_order.aux

def vonNeuman_perm.linear_order.aux : ¡vonNeumann ↪ (vonNeumann → vonNeumann) :=
  { 
    to_fun := λ π vn, π vn,
    inj' := λ π σ h, by {simp at h, apply h}
  }

instance : linear_order ¡vonNeumann := 
  linear_order.preimage vonNeuman_perm.linear_order.aux

instance : fintype ¡vonNeumann := fintype_perm

namespace symmetries

abbreviation id' : ¡vonNeumann := equiv.refl _

abbreviation  with_op (l : list ¡vonNeumann) (op : ¡vonNeumann) := l ++ op.trans <$> l 

abbreviation symmetries.to_finset_none : list (¡vonNeumann) := pure id'
abbreviation symmetries.to_finset_reflect := with_op (pure id') reflect_nh
abbreviation symmetries.to_finset_rotate2 := with_op (pure id') (rotate_clockwise.trans rotate_clockwise)
abbreviation symmetries.to_finset_rotate4 := with_op symmetries.to_finset_rotate2 rotate_clockwise
abbreviation symmetries.to_finset_rotate8 : list (¡vonNeumann):= {}
abbreviation symmetries.to_finset_rotate4reflect := with_op symmetries.to_finset_rotate4 reflect_nh

-- Yes this one is just {} also
abbreviation symmetries.to_finset_rotate8reflect := with_op symmetries.to_finset_rotate8 reflect_nh

def to_finset : symmetries → (finset ¡vonNeumann)
| symmetries.none := symmetries.to_finset_none.to_finset
| symmetries.rotate2 := symmetries.to_finset_rotate2.to_finset
| symmetries.rotate4 := symmetries.to_finset_rotate4.to_finset
| symmetries.rotate8 := symmetries.to_finset_rotate8.to_finset
| symmetries.rotate4reflect := symmetries.to_finset_rotate4reflect.to_finset
| symmetries.rotate8reflect := symmetries.to_finset_rotate4reflect.to_finset
| symmetries.reflect := symmetries.to_finset_reflect.to_finset
| symmetries.permute := finset.univ

end symmetries

def finset.as_list {α β : Type} (f : list α → β) (p : _) : finset α → β
  | ⟨ms, ms_no_dup⟩ := quotient.lift f p ms

def finmap.as_list {α : Type} {β : α → Type} {γ : Type} (f : list (sigma β) → γ) (p : _) : finmap β → γ
  | ⟨ms, nodup⟩ := quotient.lift f p ms

def on_equiv {α β} (π : α ≃ β) (f : β → β) (a : α) : α := π.symm (f (π a))

lemma on_equiv.id {α β} (π : α ≃ β) (a : α) :
  on_equiv π id a = a := equiv.coe_coe_symm _ _

@[simp]
lemma on_equiv.functorial {α β} (π : α ≃ β) (f g : β → β) (a : α) :
  on_equiv π f (on_equiv π g a) = on_equiv π (f ∘ g) a := 
by {
  unfold on_equiv,
  rw equiv.coe_coe_symm,
}

def template.precompose {α} (t : template α) (f : vonNeumann → vonNeumann) : template α := 
  on_equiv template.read (λ t io nv, t io (f nv)) t

def template.precompose_id {α} (t : template α) : t.precompose id = t :=
by {
  unfold template.precompose,
  unfold id,
  have : (λ (t : inside_outside → vonNeumann → α) (io : inside_outside) (nv : vonNeumann), t io nv) = id,
  { funext, unfold id},
  rw this,
  apply on_equiv.id,
}

lemma template.precompose_functorial {α} (t : template α) (f g : vonNeumann → vonNeumann) :
  t.precompose (f ∘ g) = (t.precompose f).precompose g := 
  by {
    unfold template.precompose,
    rw on_equiv.functorial,
  }

def on_rule {α} (π : ¡vonNeumann) : ¡(Σ _:template α, template α) :=
  { 
    to_fun := λ rule, ⟨rule.1.precompose π, rule.2.precompose π⟩,
    inv_fun := λ rule, ⟨rule.1.precompose π.symm, rule.2.precompose π.symm⟩,
    left_inv :=
    by {
      intro x,
      obtain ⟨lhs, rhs⟩ := x,
      simp only,
      repeat {rw ← template.precompose_functorial},
      unfold function.comp,
      simp_rw equiv.coe_coe_symm π,
      have : (λ (x : vonNeumann), x) = id := by {funext, simp},
      simp_rw this,
      simp_rw template.precompose_id,
      split; refl,
    },
    right_inv := 
    by {
      intro x,
      obtain ⟨lhs, rhs⟩ := x,
      simp only,
      repeat {rw ← template.precompose_functorial},
      unfold function.comp,
      simp_rw equiv.coe_symm_coe π,
      have : (λ (x : vonNeumann), x) = id := by {funext, simp},
      simp_rw this,
      simp_rw template.precompose_id,
      split; refl,
    }
  }

def alist.elaborate {α} [linear_order α] (πs : finset ¡vonNeumann) (base : alist (λ_ : template α, template α))  : 
  alist (λ_ : template α, template α) :=
    (has_seq.seq (πs.map (equiv.to_fun ∘ on_rule)) base.to_finset).to_alist

def rules.elaborate {α} [linear_order α]
  (base : template α ~> template α) (sym : symmetries) : template α ~> template α :=
   base.lift_on (alist.elaborate sym.to_finset)

def LHZ := rules.elaborate LHZ_base symmetries.rotate4

inductive step {α} [linear_order α] (rules : template α ~> template α) {n m : ℕ} : 
  ACA_board (n+1) (m+1) α → ACA_board (n+1) (m+1) α → Prop
  | intro : ∀ (p : fin (n+1) × fin (m+1)) (mat : ACA_board (n+1) (m+1) α) {b},
    b ∈ rules.find (read_template mat p) → step mat (write_template mat p b)

instance {α} [fintype α] : fintype (xcell α) :=
  {
    elems := finset.map ⟨xcell.mk, by {intros a₁ a₂ h, injection h}⟩ (fintype.elems _),
    complete := by {
      intros x,
      cases x,
      rw finset.mem_map,
      simp_rw exists_prop,
      simp_rw function.embedding.coe_fn_mk,
      rw exists_eq_right,
      apply fintype.complete,
    }
  }

instance {α} [fintype α] (n m) : fintype (ACA_board n m α) := 
{ 
  elems := finset.map ⟨aMatrix.mk, by {intros a₁ a₂ h, injection h}⟩ (fintype.elems _),
  complete := by {
    intros x,
    cases x,
    rw finset.mem_map,
    simp_rw exists_prop,
    simp_rw function.embedding.coe_fn_mk,
    use x,
    split,
    apply fintype.complete,
    refl
  }
}

def is_head {n m} (mat : ACA_board (n+1) (m+1) bool) (pos : fin (n+1) × fin (m+1)) : Prop :=
  read_template mat pos ∈ LHZ

instance {n m} (mat : ACA_board (n+1) (m+1) bool) (pos : fin (n+1) × fin (m+1)) : decidable (is_head mat pos) :=
  if H : LHZ.contains (read_template mat pos)
    then is_false sorry
    else is_true sorry

theorem LHZ_preserves_heads (n m : ℕ) (m₁ m₂ : ACA_board (n+1) (m+1) bool) (h : step LHZ m₁ m₂) :
  fintype.card {p // is_head m₁ p} = fintype.card {p // is_head m₂ p} := {

  }