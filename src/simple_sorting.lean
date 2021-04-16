import data.multiset.basic

import data.list

inductive sorted {α} [has_le α] : list α → Prop
  | nil : sorted []
  | single {x : α} : sorted [x]
  | cons {x y: α} {ys : list α} : x ≤ y → sorted (y :: ys) → sorted (x :: y :: ys)

inductive sorted' {α} [has_le α] : list α → Prop
  | nil : sorted' []
  | cons {x : α} {xs : list α} : (∀ y, y ∈ xs → x ≤ y) → sorted' xs → sorted' (x :: xs)

lemma sorted_iff_sorted' {α} [preorder α] {l : list α} : sorted l ↔ sorted' l :=
  by {
    induction l,
    case nil {exact ⟨λ _, sorted'.nil, λ _, sorted.nil⟩},
    case cons {
      induction l_tl,
      case nil {
        split; intros h; clear h; constructor,
        {intros y y_in_nil, cases y_in_nil},
        apply sorted'.nil,
      },
      case cons {
        split; intros h; cases h with a b rel_hyp ind_hyp rel_hyp ind_hyp,
        {
          constructor,
          intros y y_in,
          cases y_in,
          {rw y_in, assumption},
          {
            transitivity l_tl_hd, 
            exact rel_hyp,
            have : sorted' (l_tl_hd :: l_tl_tl) := l_ih.mp ind_hyp,
            cases this with _ _ sorted'_hyp sorted'_ind,
            apply sorted'_hyp,
            apply y_in,
          },
          {exact l_ih.mp ind_hyp},
        },
        {
          {
            apply sorted.cons _ (l_ih.mpr ind_hyp),
            apply rel_hyp,
            exact list.mem_cons_self l_tl_hd l_tl_tl,
          },
        },
      },
    },
  }

def is_sorting_of {α} [preorder α] (l': list α) (l) := sorted l' ∧ list.perm l' l

lemma sorted.tail {α} [preorder α] (l_hd : α) : ∀ (l_tl : list α), sorted (l_hd :: l_tl) → sorted l_tl 
  | [] sorted.single := sorted.nil
  | (l_tl_hd :: l_tl_tl) (sorted.cons x_le_y ind_hyp) := ind_hyp

def insert' {α} [linear_order α] : ∀ (x : α) (l : list α), list α
  | x [] := [x]
  | x (y::ys) :=
    if x ≤ y
      then x :: y :: ys
      else y :: insert' x ys

lemma insert_perm {α} [linear_order α] (x : α) (l : list α) : list.perm (x :: l) (insert' x l) :=
  by {
    induction l; unfold insert',
    split_ifs,
    refl,
    transitivity (l_hd :: x :: l_tl); try {constructor}; exact l_ih,
  }


lemma insert_sorted {α} [linear_order α] (x : α) (l : list α) : sorted l → sorted (insert' x l) :=
  by {
    intros h,
    rw sorted_iff_sorted' at h,
    induction h with z zs z_le sorted'_zs,
    {unfold insert', apply sorted.single},
    {
      unfold insert' at *,
      split_ifs,
      {
        apply sorted.cons h,
        rw sorted_iff_sorted',
        apply sorted'.cons z_le sorted'_zs,
      },
      {
        rw sorted_iff_sorted',
        apply sorted'.cons,
        intros y y_in,
        apply z_le,
        c
        rw list.perm.mem_iff (insert_perm zs ),
      }
    }
  }

def insert_sort {α} [linear_order α] : list α → list α := list.foldr insert' []

lemma insert_sort {α} [linear_order α] (l : list α) : is_sorting_of (insert_sort l) l :=
  by {
    induction l,
    case nil {exact ⟨sorted.nil, list.perm.nil⟩},
    case cons {
      obtain ⟨l_tl_sorted, l_tl_perm⟩ := l_ih,
      split,
      have H : exists l_hd' l_tl', (l_hd' :: l_tl') = insert_sort (l_hd :: l_tl),
        {unfold insert_sort, simp,  }

    }
  }