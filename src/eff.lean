import tactic

section

universes u
parameter (F : Type u → Type u)

structure interpreter (m : Type u → Type u) :=
  (monad_m : monad m)
  (lawful : is_lawful_monad m)
  (on_prompt : ∀ {α : Type u}, F α → m α)

def mk_interpreter {m} [h_1 : monad m] [h_2 : is_lawful_monad m] (p : ∀ α, F α → m α) :=
  {interpreter. on_prompt := p, monad_m := h_1, lawful := h_2}

structure eff (α : Type u) : Type (u + 1) := 
  (run : ∀ {m : Type u → Type u} (i : interpreter m), m α)

def eff.run' {m} [h_1 : monad m] [h_2 : is_lawful_monad m] {α} (e : eff α) (p : ∀ α, F α → m α):=
  e.run $ mk_interpreter p

def eff.ext (α : Type u) : ∀ (a b : eff α), (∀ {m} (i : interpreter m), a.run i = b.run i) → a = b
  | ⟨a⟩ ⟨b⟩ H := by {simp, funext m i, exact H i}

instance eff.monad : monad eff :=
  { monad.
    map := λ {α β : Type u} (f : α → β) (x : eff α), ⟨λ m i,
        @functor.map m i.monad_m.to_functor α β f (x.run i)⟩,

    pure := λ {α} (a : α), ⟨λ m i, @has_pure.pure m i.monad_m.to_has_pure α a⟩,

    seq := λ {α β} (f : eff (α → β) ) (x : eff α), ⟨λ  m i,
        @has_seq.seq m i.monad_m.to_has_seq α β (f.run i) (x.run i)⟩,

    seq_left :=
      λ {α β} (ma : eff α) (mb : eff β), ⟨λ m i,
        @has_seq_left.seq_left m i.monad_m.to_has_seq_left α β (ma.run i) (mb.run i)⟩,

    seq_right :=
      λ {α β} (ma : eff α) (mb : eff β), ⟨λ m i,
        @has_seq_right.seq_right m i.monad_m.to_has_seq_right α β (ma.run i) (mb.run i)⟩,

    bind :=
      λ {α β} (ma : eff _) (fm : _ → eff _), ⟨λ m i,
        @has_bind.bind m i.monad_m.to_has_bind _ _ (ma.run i) (λ a, (fm a).run i)⟩,
  }

theorem id_map_aux {m : Type u → Type u} [monad m] [is_lawful_monad m] {α} (x : m α) 
  : id <$> x = x := by {apply id_map}

theorem comp_map_aux {m} [monad m] [is_lawful_monad m] {α β γ : Type u} (f : α → β) (g : β → γ) (x : m α) :
  (g ∘ f) <$> x = g <$> f <$> x := by {apply comp_map}

instance eff.lawful_functor : is_lawful_functor eff :=
  { is_lawful_functor.
    id_map := λ α x, by
      { unfold_projs, simp,
        apply eff.ext,
        intros,
        apply @id_map_aux _ _ _,
        exact i.lawful,
      },
    comp_map := λ α β γ f g x, by
      {
        unfold_projs, simp, funext, apply @comp_map_aux _ _ _, exact i.lawful,
      }
  }

theorem pure_seq_eq_map_aux (α β) (m) [monad m] [is_lawful_monad m] (x : m α) (g : α → β) : pure g <*> x = g <$> x :=
  by {apply pure_seq_eq_map}

theorem map_pure_aux (α β) (m) [monad m] [is_lawful_monad m] (x : α) (g : α → β) : g <$> (pure x : m α) = pure (g x) :=
  by {apply map_pure}

theorem seq_pure_aux (α β : Type u) (m) [monad m] [is_lawful_monad m] (x : α) (g : m (α → β)) : g <*> (pure x : m α) = (λ f : α → β, f x) <$> g :=
  by {apply seq_pure}

theorem seq_assoc_aux (α β γ: Type u) (m) [monad m] [is_lawful_monad m] (x : m α) (g : m (α → β)) (h : m (β → γ))
  : h <*> (g <*> x) = function.comp <$> h <*> g <*> x :=
  by {apply seq_assoc}

theorem seq_left_eq_aux (α β) (m) [monad m] [is_lawful_monad m] (a : m α) (b : m β)
  : a <* b = function.const β <$> a <*> b :=
  by {apply seq_left_eq}

theorem seq_right_eq_aux (α β) (m) [monad m] [is_lawful_monad m] (a : m α) (b : m β)
  : a *> b = function.const α id <$> a <*> b :=
  by {apply seq_right_eq}

instance eff.lawful_applicative : is_lawful_applicative eff :=
  { is_lawful_applicative.
    pure_seq_eq_map :=
      begin
        intros,
        unfold_projs,
        simp,
        funext,
        apply @pure_seq_eq_map_aux _ _ _ _ _,
        exact i.lawful
      end,
    map_pure :=
      begin
        intros,
        unfold_projs,
        simp,
        funext,
        apply @map_pure_aux _ _ _ _ _,
        exact i.lawful
      end,
    seq_pure :=
      begin
        intros,
        unfold_projs,
        simp,
        funext,
        apply @seq_pure_aux _ _ _ _ _,
        exact i.lawful
      end,
    seq_assoc :=
      begin
        intros,
        unfold_projs,
        simp,
        funext,
        apply @seq_assoc_aux _ _ _ _ _ _ _,
        exact i.lawful
      end,
    seq_left_eq :=
      begin
        intros,
        unfold_projs,
        simp,
        funext,
        apply @seq_left_eq_aux _ _ _ _ _ _ _,
        exact i.lawful
      end,
    seq_right_eq :=
      begin
        intros,
        unfold_projs,
        simp,
        funext,
        apply @seq_right_eq_aux _ _ _ _ _ _ _,
        exact i.lawful
      end,
    .. eff.lawful_functor
  }

instance eff.lawful_monad : is_lawful_monad (eff) :=
  { is_lawful_monad.
    pure_bind := λ α β x f,
      begin
        unfold_projs,
        simp,
        apply eff.ext; intros,
        transitivity (λ a : α, (f a).run i) x,
        apply @pure_bind m i.monad_m i.lawful,
        simp,
      end,
    bind_assoc := λ α β γ x f g,
      begin
        unfold_projs,
        simp,
        funext,
        rw @bind_assoc m i.monad_m i.lawful,
      end,
    bind_pure_comp_eq_map := λ α β f x,
      begin
        unfold_projs,
        simp,
        funext,
        rw @bind_pure_comp_eq_map m i.monad_m i.lawful,
      end,
    bind_map_eq_seq := λ α β f ma,
      begin
        unfold_projs,
        simp,
        funext,
        rw @bind_map_eq_seq m i.monad_m i.lawful,
      end,
    .. eff.lawful_applicative
  }
end

universe u
abbreviation eff.embed {α} {F : Type u → Type u} (x : F α) : eff F α := 
  ⟨λ (m : Type u → Type u) (i : interpreter F m), i.on_prompt x⟩

@[simp]
lemma eff.embed.def {α} {F : Type u → Type u} (x : F α) :
  eff.embed x = ⟨λ (m : Type u → Type u) (i : interpreter F m), i.on_prompt x⟩ :=
  rfl
