-- trying to formulize ideas from Efficient Building Blocks for Delay Insensitive Circuits
-- by Priyanarsan Patra and Donald S. Fussell - University of Texas at Austin

-- namespace specification

import data.list

inductive set.star {α : Type} : set (list α) → (list α) → Prop
  | nil : ∀ {s}, set.star s list.nil
  | here : ∀ s l rest, l ∈ s → set.star s rest → set.star s (l ++ rest)

inductive shuffle {α : Type} : list α → list α → list α → Prop
  | nil : shuffle [] [] []
  | from_left : ∀ {l l_left l_right} (x : α), 
    shuffle l l_left l_right → shuffle (x::l) l_left (x::l_right)
  | from_right : ∀ {l l_left l_right} (x : α),
    shuffle l l_left l_right → shuffle (x::l) (x::l_left) l_right

structure event :=
  (is_output : bool) (name : string)

postfix `!` := λ s, {event . is_output := true, name := s }
postfix `?` := λ s, {event . is_output := false, name := s }

class trace_structure (α : Type) extends has_mem (list event) α, has_emptyc α :=
  (pref : α → α)
  (and_then : α → α → α)
  (par : α → α → α)
  (nondet : α → α → α)
  (star : α → α)

abbreviation pref {α} [trace_structure α] (a : α) := trace_structure.pref a 
infix `⬝` := λ {α} [trace_structure α] (a b : α), trace_structure.and_then a b
infix `∥`:60 := λ {α} [trace_structure α] (a b : α), trace_structure.par a b
infix `|`:60 := λ {α} [trace_structure α] (a b : α), trace_structure.nondet a b
prefix `⋆`:60 := λ {α} [trace_structure α] (a : α), (trace_structure.star a : α) 

class lawful_trace_structure (α : Type) extends trace_structure α :=
  (pref_idempotent : ∀ a : α, pref (pref a) = pref a)
  (star_idempotent : ∀ a : α, ⋆(⋆a) = ⋆a)
  (and_then_assoc : ∀ a b c : α, a⬝b⬝c = a⬝(b⬝c))
  (par_assoc : ∀ a b c : α, a∥b∥c = a∥(b∥c))
  (nondet_assoc : ∀ a b c : α, a|b|c = a|(b|c))
  (star_unfold : ∀ a : α, ⋆a = (∅|(a⬝(⋆a) : α)))

def on_sets {α} (op : α → α → α → Prop) (s₀ s₁ : set α) : set α :=
  λ a, ∃ a₀ a₁, a₀ ∈ s₀ ∧ a₁ ∈ s₁ ∧ op a a₀ a₁

instance : trace_structure (set (list event) : Type) :=
{ 
  pref := λ s l, exists l', l' ∈ s ∧ l <+: l,
  and_then := on_sets (λ l l₀ l₁, l = l₀ ++ l₁),
  par := on_sets shuffle,
  nondet := set.union,
  star := set.star,
  .. set.has_mem,
  .. set.has_emptyc
}

instance : lawful_trace_structure (set (list event)) :=
{ 
  pref_idempotent := by {
    intros s,
    unfold_projs,
    ext; split; intros h; rcases h with ⟨y, y_mem, h⟩,
    {
      simp only [exists_and_distrib_right] at y_mem,
      unfold set.mem at y_mem,
      rcases y_mem with ⟨⟨z, z_in_s⟩, y_prefix⟩,
      use z,
      split, 
      {exact (set.mem.equations._eqn_1 z s).mpr z_in_s},
      {exact h},
    },
    {
      use y,
      split,
      apply (set.mem.equations._eqn_1 _ _).mpr,
      simp only [exists_and_distrib_right],
      use y, exact y_mem, exact h
    }
  },
  star_idempotent := by {
    intros s,
    unfold trace_structure.star,
    ext; split; intros h; cases h with _ _ l h_rest l_in_star star_star,
    {apply set.star.nil},
    {
      cases l_in_star,
    }
  },
  and_then_assoc := _,
  par_assoc := _,
  nondet_assoc := _,
  star_unfold := _,
  .. set.trace_structure
}

end specification