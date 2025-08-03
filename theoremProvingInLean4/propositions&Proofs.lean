variable (p q r : Prop)

-- commutativity of ∧ and ∨
theorem example1 : p ∧ q ↔ q ∧ p :=
  Iff.intro
  /- -> λ f₁ : q =>  λ f₂ : p =>  -/
  (λ f : p ∧ q => And.intro (And.right f) (And.left f))
  /- <- -/
  (λ g : q ∧ p => And.intro (And.right g) (And.left g))


theorem example2 : p ∨ q ↔ q ∨ p :=
/- Para eliminar p ⋁ q, construimos r tal que p → r e q → r
p -> q ou p
q -> q ou p

Temos p ∨ q
Mostramos p → q ∨ p
Mostramos q → q ∨ p
Concluimos que p ∨ q → q ∨ p
Temos q ∨ p
Mostramos q → p ∨ q
Mostramos p → p ∨ q
Concluimos que q ∨ p → p ∨ q
Concluimos p ∨ q ↔ q ∨ p
-/
Iff.intro
(λ h : p ∨ q => Or.elim h
  (λ h₁ : p => Or.intro_right q h₁)
  (λ h₂ : q => Or.intro_left p h₂))
(λ g : q ∨ p => Or.elim g
  (λ g₁ : q => Or.intro_right p g₁)
  (λ g₂ : p => Or.intro_left q g₂))

example : q → q ∨ p :=
  λ h₂ : q => Or.intro_left p h₂
example : p → q ∨ p :=
  λ h₁ : p => Or.intro_right q h₁
example : p → p ∨ q :=
  λ h₂ : p => Or.intro_left q h₂
example : q → p ∨ q :=
  λ h₁ : q => Or.intro_right p h₁


variable (h : Prop)

-- associativity of ∧ and ∨
theorem example3 : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
/- IDA  (p ∧ q) ∧ r → p ∧ (q ∧ r)
Temos  (p ∧ q) ∧ r := h
elim ∧ h pra obter p ∧ q := d
elim ∧ h pra obter r
elim ∧ d para obter p
elim ∧ d para obter q
intro q ∧ r
intro p ∧ (q ∧ r)
(p ∧ q) ∧ r

VOLTA p ∧ (q ∧ r) → (p ∧ q) ∧ r

Temos p ∧ (q ∧ r) =: h
elim ∧ h para obter (q ∧ r) := d
elim ∧ h para obter p
elim ∧ d para obter q
elim ∧ d para obter r
intro p ∧ q := d
intro d ∧ r
-/
Iff.intro
  (λ h : (p ∧ q) ∧ r =>
  have h₁ : p ∧ q := And.left h -- Temos p ∧ q
  have h₂ : p := And.left h₁     -- Temos p
  have h₃ : q := And.right h₁
  have h₄ : r := And.right h
  have d : (q ∧ r) := And.intro h₃ h₄
  show p ∧ (q ∧ r) from And.intro h₂ d)

  (λ h : p ∧ (q ∧ r) =>
  have h₁ : q ∧ r:= And.right h  -- Temos q ∧ r
  have h₂ : q := And.left h₁     -- Temos p
  have h₃ : r := And.right h₁
  have h₄ : p := And.left h
  have d : (p ∧ q) := And.intro h₄ h₂
  show (p ∧ q) ∧ r from And.intro d h₃)


theorem example4 : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
 /-IDA
(p ∨ q) ∨ r → p ∨ (q ∨ r)
Temos (p ∨ q) ∨ r
Precimos construir α tal que (p ∨ q) → α e r → α
Para isso, precisamos construir p → α e q → α
Qual a cara de α?
α := p ∨ (q ∨ r)
precisaremos introduzir ∨ em p e em (q ∨ r)
com isso, precisaremos construir p e (q ∨ r) a partir de (p ∨ q) ∨ r
VOLTA
p ∨ (q ∨ r) → (p ∨ q) ∨ r
 -/
Iff.intro
  (λ h => h.elim
    (λ h₂ => h₂.elim (λ hp => Or.inl hp) (λ hq => Or.inr (Or.inl hq)))
    (λ h₁ => Or.inr (Or.inr h₁)))
  sorry


example : r → p ∨ (q ∨ r) :=
  (λ f : r => Or.intro_right p (Or.intro_right q f))

example : (p ∨ q) → p ∨ (q ∨ r) := (λ f : p ∨ q => Or.intro_left r f)
-- q → p ∨ (q ∨ r)
-- q → (q ∨ r)
example : q → q ∨ r := (λ f : q => Or.intro_left r f)
-- (q ∨ r) → p ∨ (q ∨ r)
example : q ∨ r → p ∨ (q ∨ r) := (λ f : q ∨ r => Or.intro_right p f)
-- p → p ∨ (q ∨ r)
example : p → p ∨ (q ∨ r) :=
  (λ f : p => Or.intro_left r (Or.intro_left q f))


example : r → q ∨ r := (λ f : r => Or.intro_right q f)

-- distributivity
theorem example5 : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
/-
Elim p
Elim q ∨ r
elim q ∨ r
  q → β
  r → β
  α := (p ∧ q) ∨ (p ∧ r)
-/
  (λ h : p ∧ (q ∨ r) =>
  have h₁ : p := And.left h
  have h₂ : (q ∨ r) := And.right h
  have c₁ : q → (p ∧ q) := (λ f : q => And.intro h₁ f)
  have c₂ : r → (p ∧ r):= (λ f : r => And.intro h₁ f)
  have c :
  show p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) from Or.intro_right c₁ c₂)
  ()
sorry


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry


theorem example?parte1 : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
  /- Elim do or
    A gente tem q eliminar esse and em algum momento
    depois a gnt junta p e q com p e r
   -/
  λ h : p ∨ (q ∧ r) =>
  Or.elim h
  (λ hp : p =>
  have hpq : p ∨ q := Or.intro_left q hp
  have hpr : p ∨ r := Or.intro_left r hp
  And.intro hpq hpr)
  (λ f : q ∧ r =>
  have hq : q := And.left f
  have hr : r := And.right f
  have hpq : p ∨ q := Or.intro_right p hq
  have hpr : p ∨ r := Or.intro_right p hr
  And.intro hpq hpr)

theorem example?parte2 :  (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
  λ h : (p ∨ q) ∧ (p ∨ r) =>
  have h₁ : p ∨ q := And.left h
  have h₂ : p ∨ r := And.right h
  /- Tenho que mostrar que obtemos p ∨ (q ∧ r)
    Temos p ∨ q e p ∨ r
    Podemos eliminar Or em p ∨ q
      Podemos eliminar Or em p ∨ r

  -/
  λ hp : p =>
  Or.elim h₁ (λ hp : p => ) ()



-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
/-
-/
  ()
set_option linter.unusedVariables false
theorem example6parte1: (p ∧ q → r) → (p → (q → r)) :=
  λ h : p ∧ q → r => λ c₁ : p => λ c₂ : q =>
   h (And.intro c₁ c₂)

theorem example6parte2: (p → (q → r)) → (p ∧ q → r) :=
  λ h : p → (q → r) =>
  λ pq : p ∧ q =>
    have hp : p := pq.left
    have hq : q := pq.right
    have hqr : q → r := h hp
    have hr : r := hqr hq
    hr

theorem example6 : (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro
  (λ h : p → (q → r) =>
   λ pq : p ∧ q =>
    have hp : p := pq.left
    have hq : q := pq.right
    have hqr : q → r := h hp
    have hr : r := hqr hq
    hr
)

(λ h : p ∧ q → r => λ c₁ : p => λ c₂ : q =>
   h (And.intro c₁ c₂))


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

theorem example7parte1 : (((p ∨ q) → r) → (p → r) ∧ (q → r)) :=
  (λ h : ((p ∨ q) → r) =>
  /-Supor p ∨ q → r
    Entao conseguimos provar tanto r a partir de p quanto r a partir de q
    supor p e introduzir or com q
    supor q e introduzir or com p
    conjuncao dos dois
  -/
  And.intro (λ hp : p => h (Or.intro_left q hp)) (λ hq : q => h (Or.intro_right p hq)))

theorem example7parte2 : ((p → r) ∧ (q → r)) → (p ∨ q) → r :=
  /- Suponha p ∨ q
    Como a gnt tem p → r e q → r
    A gente pode eliminar p ∨ q por r
  -/
  λ h : (p → r) ∧ (q → r) =>
  have h₁ : p → r := And.left h
  have h₂ : q → r := And.right h
  λ f : p ∨ q => Or.elim f (h₁) (h₂)

theorem example7 : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
Iff.intro
  (λ h : ((p ∨ q) → r) =>
  And.intro (λ hp : p => h (Or.intro_left q hp)) (λ hq : q => h (Or.intro_right p hq)))
  (λ h : (p → r) ∧ (q → r) =>
  have h₁ : p → r := And.left h
  have h₂ : q → r := And.right h
  λ f : p ∨ q => Or.elim f (h₁) (h₂))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

theorem example8parte1 : ¬p ∧ ¬q  → ¬(p ∨ q) :=
  λ h : ¬p ∧ ¬q =>
  have hpFalse : ¬p := And.left h
  have hqFalse : ¬q := And.right h
  have hpFalseORhqFalse : ¬p ∨ ¬q := Or.intro_right hpFalse ¬q
  -- Vamos construir uma contradicao a partir de p ∨ q
  λ f : p ∨ q => p

sorry

theorem example8parte1 : ¬(p ∨ q) → ¬p ∧ ¬q := sorry

example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry


example : ¬(p ∧ ¬p) :=
  λ h : p ∧ ¬p =>
  have h₁ : p := And.left h
  have h₂ : ¬p := And.right h
  -- ¬p eh uma funcao p → False
  -- Quando a gente coloca ¬p p, a gnt ta aplicando uma funcao p → False com argumento p. O que retorna False
  show False from (And.right h) (And.left h)

example : p ∧ ¬q → ¬(p → q) :=
  λ h : p ∧ ¬ q =>
  have h₁ : p := And.left h
  have h₂ : ¬q := And.right h
  λ f : p → q =>
  have hq : q := f h₁
  show False from h₂ hq

example : ¬p → (p → q) :=
  λ h : ¬ p =>
  λ f : p => False.elim (h f)

example : (¬p ∨ q) → (p → q) :=
  λ f : ¬p ∨ q => Or.elim f (λ h : ¬ p => λ f₁ : p => False.elim (h f₁)) (λ f₂ : q => λ f₃ : p => f₂)

example : p ∨ False ↔ p :=
Iff.intro (
  λ h : p ∨ False => Or.elim h (λ hp : p => hp) (λ hFalse : False => False.elim hFalse)
) (
  λ hp : p => Or.intro_left False hp
)

example : p ∧ False ↔ False :=
Iff.intro (
λ h : p ∧ False => And.right h
) (
  λ hFalse : False => False.elim hFalse
)

example : (p → q) → (¬q → ¬p) :=
  λ h : p → q => λ h₁ : ¬ q => λ hp : p =>
  have hq : q := h hp
  have HFalse : False := h₁ hq
  show False from HFalse

/- Aqui vamos fazer uso da logica classica
  Vamos adicionar a lei do terceiro excluido (p ∨ ¬p)
-/

open Classical

variable (p q r : Prop)

#check em -- Posso sempre introduzir em alguma proposicao p provar alguma coisa.


#check em (¬p ∧ q)



theorem classicalExample1 : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h : p → q ∨ r =>
  have hqr : q ∨ r := h p
  λ hp : p =>
  Or.elim hqr λ hq : q =>
  have hqem : q ∨ ¬q := em hq
  sorry

#check em (q ∨ r)

theorem classicalExample2 : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h : ¬(p ∧ q) => Or.elim (em h) (λ ) ()

sorry

#check em ¬ (p ∧ q)

example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
