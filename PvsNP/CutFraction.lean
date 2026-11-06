import Init.Grind.Ordered.Rat

/-!
# Exact cut fractions and the closure parameter

Source: structural-reasoning/theory/folding/FOLDING_CLOSURE_UNIT.md,
"The bridge to the measured cut fraction". The rational ratio x is sent to
f = x/(1+x), with closure parameter k = x*x-x. Positivity makes the
denominators nonzero and gives an exact correspondence with 0 < f < 1.
These are algebraic facts, independent of measured folds, physical units,
self-reference, or claims that experimental data differ from a null model.
Real square roots and irrational golden values are outside this entry.
-/

namespace PvsNP.CutFraction

def fraction (x : Rat) : Rat := x / (1 + x)
def ratio (f : Rat) : Rat := f / (1 - f)
def closure (x : Rat) : Rat := x * x - x
def recoveredClosure (f : Rat) : Rat := f * (2 * f - 1) / (1 - f)^2

theorem denominator_pos {x : Rat} (hx : 0 < x) : 0 < 1 + x := by grind

theorem fraction_pos {x : Rat} (hx : 0 < x) : 0 < fraction x := by
  unfold fraction
  apply (Rat.lt_div_iff (denominator_pos hx)).2
  simpa using hx

theorem fraction_lt_one {x : Rat} (hx : 0 < x) : fraction x < 1 := by
  unfold fraction
  apply (Rat.div_lt_iff (denominator_pos hx)).2
  grind

theorem fraction_in_unit_interval {x : Rat} (hx : 0 < x) :
    0 < fraction x ∧ fraction x < 1 :=
  ⟨fraction_pos hx, fraction_lt_one hx⟩

theorem ratio_fraction {x : Rat} (hx : 0 < x) : ratio (fraction x) = x := by
  have hd := Rat.ne_of_gt (denominator_pos hx)
  unfold ratio fraction
  grind

theorem ratio_pos {f : Rat} (hf : 0 < f) (h1 : f < 1) : 0 < ratio f := by
  unfold ratio
  apply (Rat.lt_div_iff ((Rat.lt_iff_sub_pos f 1).1 h1)).2
  simpa using hf

theorem fraction_ratio {f : Rat} (hf : 0 < f) (h1 : f < 1) :
    fraction (ratio f) = f := by
  have hd := Rat.ne_of_gt ((Rat.lt_iff_sub_pos f 1).1 h1)
  have hp := denominator_pos (ratio_pos hf h1)
  have hn := Rat.ne_of_gt hp
  unfold fraction ratio at *
  grind

theorem fraction_injective {x y : Rat} (hx : 0 < x) (hy : 0 < y)
    (h : fraction x = fraction y) : x = y := by
  have hr := congrArg ratio h
  simpa only [ratio_fraction hx, ratio_fraction hy] using hr

theorem closure_equation (x : Rat) : x*x = x + closure x := by
  unfold closure
  grind

theorem closure_ratio {f : Rat} (h1 : f ≠ 1) :
    closure (ratio f) = recoveredClosure f := by
  have hd : 1 - f ≠ 0 := by grind
  unfold closure ratio recoveredClosure
  grind

theorem recovered_closure_fraction {x : Rat} (hx : 0 < x) :
    recoveredClosure (fraction x) = closure x := by
  rw [← closure_ratio (Rat.ne_of_lt (fraction_lt_one hx)), ratio_fraction hx]

theorem fraction_one : fraction 1 = 1/2 := by
  unfold fraction
  grind

theorem fraction_eq_half_iff {x : Rat} (hx : 0 < x) :
    fraction x = 1/2 ↔ x = 1 := by
  constructor
  · intro h
    apply fraction_injective hx (by decide : (0 : Rat) < 1)
    exact h.trans fraction_one.symm
  · rintro rfl
    exact fraction_one

/-- The cut fraction preserves every comparison of positive ratios. -/
theorem fraction_lt_iff {x y : Rat} (hx : 0 < x) (hy : 0 < y) :
    fraction x < fraction y ↔ x < y := by
  unfold fraction
  have hdx := denominator_pos hx
  have hdy := denominator_pos hy
  have hc : y / (1+y) * (1+x) = (y*(1+x))/(1+y) := by grind
  rw [Rat.div_lt_iff hdx, hc, Rat.lt_div_iff hdy]
  grind

theorem fraction_lt_half_iff {x : Rat} (hx : 0 < x) :
    fraction x < 1/2 ↔ x < 1 := by
  rw [← fraction_one]
  exact fraction_lt_iff hx (by decide)

theorem half_lt_fraction_iff {x : Rat} (hx : 0 < x) :
    1/2 < fraction x ↔ 1 < x := by
  rw [← fraction_one]
  exact fraction_lt_iff (by decide) hx

/-- The original closure equation, expressed using only the cut fraction. -/
theorem closure_equation_in_fraction {x k : Rat} (hx : 0 < x) :
    x*x = x+k ↔
      fraction x * (2*fraction x-1) = k*(1-fraction x)^2 := by
  have hr := recovered_closure_fraction hx
  have hn := Rat.ne_of_lt (fraction_lt_one hx)
  have hd : 1-fraction x ≠ 0 := by grind
  unfold recoveredClosure closure at hr
  grind

/-- k = 1 corresponds exactly to the quadratic satisfied by a golden cut.
    This states the equation over rationals, without asserting a rational root. -/
theorem unit_one_equation {x : Rat} (hx : 0 < x) :
    x*x = x+1 ↔ fraction x * fraction x + fraction x = 1 := by
  rw [closure_equation_in_fraction hx]
  grind

end PvsNP.CutFraction
