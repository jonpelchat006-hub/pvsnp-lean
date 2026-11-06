import PvsNP.Poly

/-!
# P, NP and reductions over an abstract machine model

Instead of fixing Turing machines up front, this file states the handful of
closure properties every reasonable polynomial-time model has (identity,
composition, polynomially bounded output, if-then-else, negation, ...) and
proves the classical structural theorems of NP-completeness from those
properties alone.

Why do it this way?

* The theorems here then hold for *any* concrete model that satisfies the
  interface — multi-tape Turing machines, RAMs, the λ-calculus, or a model
  taken from another library. Plugging in a real model is a later step.
* It makes the logical status of each theorem visible: everything in this
  file follows from bookkeeping. `PvsNP/Barrier.lean` then shows that this
  bookkeeping alone cannot settle P vs NP.

Faithfulness notes for the definitions (the part a reviewer must check):

* `Fn f`   — `f` is computable in polynomial time.
* `Dec d`  — the yes/no question `d` is decidable in polynomial time.
* `Ver V`  — `V x w` is computable in time polynomial in the length of `x`
             (so it can only ever read polynomially many bits of `w`).
* `InNP` bounds certificates by `|w| ≤ |g x|` for some `g` with `Fn g`.
  Because `Fn` functions have polynomially bounded output (`fn_size`), this is
  a polynomial bound; using `|g x|` rather than an arbitrary number makes the
  bound itself computable, which is required for the class to be the real NP.
  `InNP.poly_certificates` recovers the textbook shape `|w| ≤ (|x| + c)^k`.
-/

namespace PvsNP

/-- Inputs are bit strings. -/
abbrev Word := List Bool

/-- A language (decision problem) is a property of bit strings. -/
abbrev Language := Word → Prop

/-- An abstract polynomial-time computation model: just the closure
properties needed for the theory of NP-completeness. -/
structure Model where
  /-- polynomial-time computable functions -/
  Fn  : (Word → Word) → Prop
  /-- polynomial-time decidable predicates -/
  Dec : (Word → Bool) → Prop
  /-- polynomial-time (in the first argument) checkers of an input and a certificate -/
  Ver : (Word → Word → Bool) → Prop
  fn_id      : Fn (fun x => x)
  fn_comp    : ∀ {f g}, Fn f → Fn g → Fn (fun x => g (f x))
  fn_size    : ∀ {f}, Fn f → ∃ c k, ∀ x, (f x).length ≤ poly c k x.length
  fn_ite     : ∀ {d} (a b : Word), Dec d → Fn (fun x => if d x then a else b)
  dec_comp   : ∀ {f d}, Fn f → Dec d → Dec (fun x => d (f x))
  dec_not    : ∀ {d}, Dec d → Dec (fun x => !d x)
  ver_of_dec : ∀ {d}, Dec d → Ver (fun x _ => d x)
  ver_comp   : ∀ {f V}, Fn f → Ver V → Ver (fun x w => V (f x) w)

namespace Model

variable (M : Model)

/-- `L ∈ P` -/
def InP (L : Language) : Prop :=
  ∃ d, M.Dec d ∧ ∀ x, L x ↔ d x = true

/-- `L ∈ NP`: membership has short, efficiently checkable certificates. -/
def InNP (L : Language) : Prop :=
  ∃ V g, M.Ver V ∧ M.Fn g ∧ ∀ x, L x ↔ ∃ w : Word, w.length ≤ (g x).length ∧ V x w = true

/-- `L ∈ coNP`: the complement of `L` is in NP. -/
def InCoNP (L : Language) : Prop :=
  M.InNP (fun x => ¬ L x)

/-- Polynomial-time many-one (Karp) reduction `L₁ ≤ₚ L₂`. -/
def Reduces (L₁ L₂ : Language) : Prop :=
  ∃ f, M.Fn f ∧ ∀ x, L₁ x ↔ L₂ (f x)

def NPHard (L : Language) : Prop :=
  ∀ L', M.InNP L' → M.Reduces L' L

def NPComplete (L : Language) : Prop :=
  M.InNP L ∧ M.NPHard L

/-- The P vs NP question for this model: do the two classes coincide? -/
def PeqNP : Prop :=
  ∀ L, M.InP L ↔ M.InNP L

def NPeqCoNP : Prop :=
  ∀ L, M.InNP L ↔ M.InCoNP L

variable {M}

/-! ## The textbook certificate bound -/

/-- Certificates are polynomially short in the usual sense. -/
theorem InNP.poly_certificates {L : Language} (h : M.InNP L) :
    ∃ V c k, M.Ver V ∧ ∀ x, L x → ∃ w : Word, w.length ≤ poly c k x.length ∧ V x w = true := by
  obtain ⟨V, g, hV, hg, hL⟩ := h
  obtain ⟨c, k, hck⟩ := M.fn_size hg
  refine ⟨V, c, k, hV, fun x hx => ?_⟩
  obtain ⟨w, hw, hVw⟩ := (hL x).1 hx
  exact ⟨w, Nat.le_trans hw (hck x), hVw⟩

/-! ## Reductions form a preorder -/

theorem reduces_refl (L : Language) : M.Reduces L L :=
  ⟨fun x => x, M.fn_id, fun _ => Iff.rfl⟩

theorem reduces_trans {L₁ L₂ L₃ : Language} :
    M.Reduces L₁ L₂ → M.Reduces L₂ L₃ → M.Reduces L₁ L₃ := by
  rintro ⟨f, hf, h₁⟩ ⟨g, hg, h₂⟩
  exact ⟨fun x => g (f x), M.fn_comp hf hg, fun x => (h₁ x).trans (h₂ (f x))⟩

/-! ## Closure of P and NP -/

/-- P is closed downward under reductions. -/
theorem InP.of_reduces {L₁ L₂ : Language} (hr : M.Reduces L₁ L₂) (h : M.InP L₂) :
    M.InP L₁ := by
  obtain ⟨f, hf, hfL⟩ := hr
  obtain ⟨d, hd, hdL⟩ := h
  exact ⟨fun x => d (f x), M.dec_comp hf hd, fun x => (hfL x).trans (hdL (f x))⟩

/-- NP is closed downward under reductions. -/
theorem InNP.of_reduces {L₁ L₂ : Language} (hr : M.Reduces L₁ L₂) (h : M.InNP L₂) :
    M.InNP L₁ := by
  obtain ⟨f, hf, hfL⟩ := hr
  obtain ⟨V, g, hV, hg, hL⟩ := h
  exact ⟨fun x w => V (f x) w, fun x => g (f x), M.ver_comp hf hV, M.fn_comp hf hg,
    fun x => (hfL x).trans (hL (f x))⟩

/-- P is closed under complement. -/
theorem InP.compl {L : Language} (h : M.InP L) : M.InP (fun x => ¬ L x) := by
  obtain ⟨d, hd, hdL⟩ := h
  refine ⟨fun x => !d x, M.dec_not hd, fun x => ?_⟩
  show ¬ L x ↔ (!d x) = true
  rw [hdL x]
  cases d x <;> simp

/-- Double complement (classical). -/
theorem compl_compl (L : Language) : (fun x => ¬ ¬ L x) = L := by
  funext x
  exact propext ⟨Classical.byContradiction ∘ fun h h' => h h', fun h h' => h' h⟩

/-- **P ⊆ NP**: a language decidable in polynomial time needs no certificate. -/
theorem P_subset_NP {L : Language} (h : M.InP L) : M.InNP L := by
  obtain ⟨d, hd, hdL⟩ := h
  refine ⟨fun x _ => d x, fun x => x, M.ver_of_dec hd, M.fn_id, fun x => ?_⟩
  rw [hdL x]
  exact ⟨fun h => ⟨[], Nat.zero_le _, h⟩, fun ⟨_, _, h⟩ => h⟩

/-! ## NP-hardness and NP-completeness -/

/-- Hardness propagates forward along reductions. -/
theorem NPHard.of_reduces {L₁ L₂ : Language} (h : M.NPHard L₁) (hr : M.Reduces L₁ L₂) :
    M.NPHard L₂ :=
  fun L' hL' => reduces_trans (h L' hL') hr

/-- How every NP-completeness proof after Cook–Levin works: reduce a known
NP-complete problem to the new one, and check the new one is in NP. -/
theorem NPComplete.of_reduces {L₁ L₂ : Language} (h : M.NPComplete L₁)
    (hr : M.Reduces L₁ L₂) (hNP : M.InNP L₂) : M.NPComplete L₂ :=
  ⟨hNP, h.2.of_reduces hr⟩

/-- If any NP-hard problem is in P, then P = NP. -/
theorem PeqNP_of_NPHard_in_P {L : Language} (hH : M.NPHard L) (hP : M.InP L) : M.PeqNP :=
  fun L' => ⟨P_subset_NP, fun hL' => InP.of_reduces (hH L' hL') hP⟩

/-- **The central fact about NP-completeness**: an NP-complete problem is in P
exactly when P = NP. So P vs NP is a question about any single NP-complete
problem, e.g. SAT. -/
theorem NPComplete.inP_iff_PeqNP {C : Language} (hC : M.NPComplete C) :
    M.InP C ↔ M.PeqNP :=
  ⟨PeqNP_of_NPHard_in_P hC.2, fun h => (h C).2 hC.1⟩

/-- Contrapositive form: to prove P ≠ NP it suffices to show one NP-complete
problem is not in P — and that is also necessary. -/
theorem NPComplete.not_inP_iff_PneNP {C : Language} (hC : M.NPComplete C) :
    ¬ M.InP C ↔ ¬ M.PeqNP :=
  not_congr hC.inP_iff_PeqNP

/-! ## Consequences of P = NP -/

/-- **P = NP implies NP = coNP.** -/
theorem NPeqCoNP_of_PeqNP (h : M.PeqNP) : M.NPeqCoNP := by
  intro L
  constructor
  · intro hL
    exact P_subset_NP ((h L).2 hL).compl
  · intro hL
    have hc : M.InP (fun x => ¬ ¬ L x) := ((h _).2 hL).compl
    rw [compl_compl] at hc
    exact P_subset_NP hc

/-- Contrapositive: proving NP ≠ coNP would already prove P ≠ NP. -/
theorem PneNP_of_NPneCoNP (h : ¬ M.NPeqCoNP) : ¬ M.PeqNP :=
  fun h' => h (NPeqCoNP_of_PeqNP h')

/-- **If P = NP, every nontrivial language in P is NP-complete** — even
"is the first bit a 1?". This is why P = NP would collapse the whole
NP-completeness hierarchy. -/
theorem NPComplete_of_PeqNP (h : M.PeqNP) {L : Language} (hL : M.InP L)
    {a b : Word} (ha : L a) (hb : ¬ L b) : M.NPComplete L := by
  refine ⟨P_subset_NP hL, fun L' hL' => ?_⟩
  obtain ⟨d, hd, hdL⟩ := (h L').2 hL'
  refine ⟨fun x => if d x then a else b, M.fn_ite a b hd, fun x => ?_⟩
  show L' x ↔ L (if d x then a else b)
  rw [hdL x]
  cases d x <;> simp [ha, hb]

end Model

end PvsNP
