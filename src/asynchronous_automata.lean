import .hitchhike
import .make_ruletable

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

def template.read {α} (arr : template α) (io : inside_outside) (dir : vonNeumann) : α :=
  arr.to_array.read (template.read_aux (io, dir))

def template.from_fun {α} (f : inside_outside → vonNeumann → α) : template α :=
  ⟨⟨λ ix, function.uncurry f (template.read_aux.inv_fun ix)⟩⟩

def ACA_rule (α) := (template α → template α → Prop)

def ACA_board (n m) (α : Type) := aMatrix n m (vonNeumann → α) 

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
  (mat : aMatrix (n+1) (m+1) (vonNeumann → α)) 
  (ix : fin (n+1) × fin (m+1)) : inside_outside → vonNeumann → α
  | inside dir := (mat.read ix) dir
  | outside dir := 
    let offset : (fin (n+1) × fin (m+1)) := dir.to_index in
    mat.read (ix.1 + offset.1, ix.2 + offset.2) (-dir)

def read_template {n m} {α : Type} 
  (mat : aMatrix (n+1) (m+1) (vonNeumann → α)) 
  (ix : fin (n+1) × fin (m+1)) :
  template α := template.from_fun (read_template.aux mat ix)

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

instance {α} [decidable_eq α] : decidable_eq (vonNeumann → α) :=
  by {
    intros a b,
    have H : (a = b) ↔ (∀ nv, a nv = b nv) := by {split; intros h, {intros x, rw h}, funext, apply h},
    rw H,
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

def ACA_rules.from_list : list (array 2 (array 8 (fin 2))) →  rbmap (template bool) (template bool)
  | l :=
    let to_templates : array 2 (array 8 (fin 2)) → (template bool × template bool) :=
      λ arr, 
        match (arr.map array.to_template).to_vector with
        | ⟨[old, new], _⟩ := ⟨old, new⟩
        end
      in
    (l.map to_templates)

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

def LHZ_base : rbmap (template bool) (template bool) :=
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

