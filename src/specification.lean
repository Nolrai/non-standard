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

abbreviation run := list event

