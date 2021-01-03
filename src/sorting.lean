import data.list.chain
import data.list
import control.monad.basic
import control.monad.writer

inductive 

inductive sorting_code (size : nat) : Type → Type 2
  | pure_ : ∀ {α : Type}, α → sorting_code α
  | bind_ : ∀ α β (ma : sorting_code α) (fm : α → sorting_code β), sorting_code β
  | swap : ∀ (i j : fin size), sorting_code unit
  | comp : ∀ (i j : fin size), sorting_code bool

open sorting_code

instance sorting.has_bind (size : nat) : has_bind (sorting_code size) :=
  {bind := λ α β mx mf, sorting_code.bind_ α β mx mf} 

instance sorting.has_pure (size : nat) : has_pure (sorting_code size) :=
  {pure := λ α x, sorting_code.pure_ x} 

def sorting.map (size) (α β : Type) (f : α → β) (mx : sorting_code size α) : sorting_code size β :=
  bind_ _ _ mx (pure_ ∘ f)

def array.swap {size} {α} : array size α → fin size → fin size → array size α
  | arr i j := (arr.write i (arr.read j)).write j (arr.read i) 

def sorting_code.width {size} : ∀ {α}, sorting_code size α → ℕ 
  | _ (pure_ a) := 1
  | _ (bind_ β γ ma fm) := 1 + ma.width
  | unit (swap i j) := 1
  | bool (comp i j) := 1

def d_uncurry {α} {β : α → Type} {γ : ∀ {x}, β x → Type} 
  (f : ∀ (x : α) (y : β x), γ y) (y : (Σ x, β x)) : γ (y.snd) := f y.fst y.snd

def sorting_code.measure {size} : (Σ' (α : Type), sorting_code size α) → ℕ 
  | ⟨_, code⟩ := code.width

lemma run_aux (size : ℕ) (κ γ : Type)
  (ma : sorting_code size γ)
  (fm : γ → sorting_code size κ) :
  sorting_code.measure ⟨γ, ma⟩ <
    sorting_code.measure ⟨κ, bind_ γ κ ma fm⟩ :=
begin
  unfold sorting_code.measure,
  unfold sorting_code.width,
  exact lt_one_add (sorting_code.width ma)
end

def sorting.run (m : Type → Type) (β size)
  [monad m]
  [monad_state (array size β) m]
  [monad_reader (β → β → bool) m]
  [monad_writer (nat × nat) m] 
  :
  ∀ α, sorting_code size α → m α 
| _ (pure_ a) := pure a
| _ (bind_ γ κ mx fm) := 
  have mx_aux : sorting_code.measure ⟨γ, mx⟩ < sorting_code.measure ⟨κ, bind_ γ κ mx fm⟩ := 
    begin apply run_aux end,
  have fm_aux : ∀ a : sorting_code size κ, sorting_code.measure ⟨κ, a⟩ < sorting_code.measure ⟨κ, bind_ γ κ mx fm⟩ := sorry,
  bind (sorting.run _ mx) (fix (f γ) ∘ fm)
| unit (swap i j) := tell (0,1) >> modify (λ arr, arr.swap i j) 
| bool (comp i j) :=
  do
  c <- read,
  arr <- get,
  tell (1,0),
  pure (c (arr.read i) (arr.read j))
  using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf sorting_code.measure⟩]}


instance (size : nat) : functor (sorting_code size) :=
  {
    map := sorting.map size
  }

instance (size : nat) : is_lawful_functor (sorting_code size) := 
  { map_const_eq := λ _ _, rfl,
  id_map := λ α x, begin unfold functor.map sorting.map, end,
  comp_map := _ }
