-- trying to formulize ideas from Efficient Building Blocks for Delay Insensitive Circuits
-- by Priyanarsan Patra and Donald S. Fussell - University of Texas at Austin
import data.finset
import data.multiset.nodup

namespace specification

structure event :=
  (is_output : bool) (name : string)

postfix ! := λ s, {event . is_output := true, name := s }
postfix ? := λ s, {event . is_output := false, name := s }

def behavior := finset (list event)

lemma list.inits.nodup {α} (l : list α) : l.inits.nodup :=
  by {
    induction l, 
    
    case nil {
      apply list.nodup_cons.mpr,
      simp only [list.not_mem_nil, not_false_iff, and_self, list.nodup_nil],
    },

    case cons {
      simp only [true_and, list.inits, list.mem_map, exists_false, not_false_iff, list.nodup_cons, and_false],
      apply list.nodup_map list.cons_injective l_ih,
    }
  }

def prefix_close {α} [decidable_eq α] (s : finset (list α)) : finset (list α) :=
  s.bUnion (λ l, ⟨l.inits, list.inits.nodup l⟩)

def and_then {α} [decidable_eq α] (s₀ s₁ : finset (list α)) : finset (list α) :=
  s₀.bUnion (λ l₀, s₁.map (⟨(λ l₁, l₀ ++ l₁), by {refine list.append_right_injective l₀}⟩ )

def shuffle {α} [decidable_eq α] : list α → list α → finset (list α)
  | [] l₁ := {l₁}
  | l₀ [] := {l₀}
  | (x₀::xs₀) (x₁::xs₁) := (shuffle xs₀ (x₁ :: xs₁)).map ⟨λ l, 

end specification
