import data.pfun

universes u

structure interpreter (F : Type u → Type u) : Type (u +1) :=
  (m : Type u → Type u) (monad_m : monad m) (lawful : is_lawful_monad m) (on_prompt (α : Type u) : F α → m α)

def eff (F : Type u → Type u) (α : _) := Π i : interpreter F, i.m α

abbreviation interpreter.run {F α} (i : interpreter F) (x : eff F α) := x i
abbreviation eff.run {F α} (x : eff F α) (i : interpreter F) := x i

abbreviation pure' (m : Type u → Type u) (h : monad m) : ∀ {α} (x : α), m α := λ α x, pure x
def  bind' (m : Type u → Type u) (h : monad m) : ∀ {α} (x : m α) {β} (f : α → m β), m β := 
  λ α x β f, bind x f
def  map' (m : Type u → Type u) (h : monad m) : ∀ {α β} (f : α → β) (x : m α), m β :=
  λ α β f x, f <$> x
def  seq' (m : Type u → Type u) (h : monad m) : ∀ {α β : Type u} (mf : m (α → β)) (x : m α), m β :=
  λ α β mf x, mf <*> x

def eff.pure {α} {F} (x : α) : eff F α :=
  λ i, pure' i.m i.monad_m x
def eff.bind {α β F} (x : eff F α) (f : α → eff F β) : eff F β :=
  λ i, bind' i.m i.monad_m (x i) (i.run ∘ f)

def eff.map {α β : Type u} {F} (f : α → β) (effA : eff F α) : eff F β := 
  λ i, map' i.m i.monad_m f (i.run effA)
def eff.seq {α β : Type u} {F} (effF : eff F (α → β)) (x : eff F α) : eff F β := 
  λ i, seq' i.m i.monad_m (i.run effF) (i.run x)

instance (F : Type u → Type u) : monad (eff F) :=
{ map := λ α β, eff.map,
  pure := λ α, eff.pure,
  seq := λ α β, eff.seq,
  bind := λ α β, eff.bind }

-- lemma eff.id_map_aux (m : Type u → Type u) (h: monad m) (h1 : is_lawful_monad m) {α : Type u} (x : m α) :
--   x >>= return = x :=
-- begin
--   exact bind_pure x
-- end

#print is_lawful_monad

lemma eff.id_map_aux (m : Type u → Type u) (h : monad m) (h' : is_lawful_monad m) 
  {α : Type u} (x : m α) : id <$> x = x :=
  begin
    apply @id_map',
  end

lemma eff.id_map (F : Type u → Type u) {α : Type u} (x : eff F α) : id <$> x = x :=
  begin
    unfold_projs,
    unfold eff.map map',
    funext,
    apply eff.id_map_aux i.m i.monad_m i.lawful,
  end

lemma eff.comp_map_aux (m : Type u → Type u) (m' : monad m) (m'' : is_lawful_monad m) {α β γ} :
  ∀ (h : β → γ) (g : α → β) (x : m α), (h ∘ g) <$> x = h <$> g <$> x :=
  begin
    intros,
    exact comp_map g h x,
  end
  
lemma eff.comp_map  
  (F : Type u → Type u) {α β γ : Type u}
  (g : α → β)
  (h : β → γ)
  (x : eff F α) :
  (h ∘ g) <$> x = h <$> g <$> x :=
begin
  unfold_projs,
  simp,
  unfold eff.map map',
  funext,
  transitivity (map' i.m i.monad_m h (map' i.m i.monad_m g (i.run x))),
  unfold map',
  apply eff.comp_map_aux _ _ i.lawful,
  unfold map',
end

lemma eff.pure_bind_ {α β : Type u}
  (g : α)
  (m : Type u → Type u)
  (H : monad m) 
  (H' : is_lawful_monad m)
  (ff : α → m β)
  : return g >>= ff = ff g :=
begin
  apply pure_bind,
end

lemma eff.pure_seq_eq_map (F : Type u → Type u) {α β : Type u}
  (g : α → β)
  (x : eff F α) :
  pure g <*> x = g <$> x :=
begin
  unfold_projs, 
  simp,
  unfold eff.map eff.pure eff.seq eff.bind,
  unfold bind' map' seq',
  funext,
  transitivity seq' i.m i.monad_m (pure' i.m i.monad_m g) (i.run x),
  reflexivity,
  unfold seq',
  rw ← @pure_seq_eq_map i.m i.monad_m.to_applicative i.lawful.to_is_lawful_applicative,
  end

lemma eff.map_pure (F : Type u → Type u) {α β : Type u}
  (g : α → β)
  (x : α) :
  g <$> (pure x : eff F α) = pure (g x) :=
begin
  unfold_projs,
  unfold eff.map eff.pure eff.bind bind',
  funext,
  transitivity (i.run ∘ eff.pure ∘ g) x,
  apply eff.pure_bind_,
  exact i.lawful,
  simp,
  refl,
end

lemma eff.seq_pure (F : Type u → Type u) {α β : Type u}
  (g : eff F (α → β))
  (x : α) :
  g <*> pure x = (λ (g : α → β), g x) <$> g :=
begin
  unfold_projs,
  unfold eff.pure eff.seq eff.map eff.bind bind',
  funext,
  congr,
  funext,
  simp,
  transitivity (i.run ∘ eff.pure ∘ f') x,
  apply eff.pure_bind_,
  {exact i.lawful},
  simp,
end

 lemma eff.seq_assoc_aux : ∀ α (F) (i : interpreter F) (x : i.m α) (β) (f : α → β), 
  bind' i.m i.monad_m x (i.run ∘ eff.pure ∘ f) = map' i.m i.monad_m f x :=
  begin
    unfold bind' map',
    clear_except,
    intros,
    transitivity (bind' _ _ x (pure' _ i.monad_m ∘ f)),
    {unfold bind', reflexivity},
    unfold bind',
    apply @bind_pure_comp_eq_map i.m i.monad_m i.lawful,
  end

lemma eff.seq_assoc (F : Type u → Type u) {α β γ : Type u}
  (x : eff F α)
  (g : eff F (α → β))
  (h : eff F (β → γ)) :
  h <*> (g <*> x) = function.comp <$> h <*> g <*> x :=
begin
  unfold_projs,
  simp,
  unfold eff.map eff.seq eff.bind eff.pure,
  funext,
  simp_rw eff.seq_assoc_aux,
  unfold bind' map',
end


instance (F : Type u → Type u) : is_lawful_monad (eff F) :=
{ map_const_eq := by {intros, reflexivity},
  id_map := λ α, eff.id_map F,
  comp_map := by {apply eff.comp_map},
  seq_left_eq := λ _ _ _ _, rfl,
  seq_right_eq := λ _ _ _ _, rfl,
  pure_seq_eq_map := by {apply eff.pure_seq_eq_map },
  map_pure := by {apply eff.map_pure},
  seq_pure := by {apply eff.seq_pure},
  seq_assoc := by {intros, extract_goal},
  bind_pure_comp_eq_map := _,
  bind_map_eq_seq := _,
  pure_bind := _,
  bind_assoc := _ }