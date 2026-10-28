import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalNormalUnitRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalFrame

/-! # Rational Unit Neighborhood -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: genuine unit-valued local representatives of a moved rational line-bundle section -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_rationalSection_unit_neighborhood (a : X.functionFieldˣ) (x : X)
    (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (ha : L.rationalSectionPointDivisorWithCoefficient a x = 0) :
    ∃ (U : X.Opens) (_ : U ≤ L.trivializingOpen x) (hxU : x ∈ U) (u : Γ(X, U)ˣ),
      letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm U u = a * L.rationalSectionCoordinate x := by
  have hzero : X.ord (a * L.rationalSectionCoordinate x).val x = 0 := by
    exact (L.rationalSectionPointDivisorWithCoefficient_apply a x).symm.trans ha
  obtain ⟨V, _, hxV, v, hv⟩ := RationalNormalUnitRestriction.BundleCycles.exists_regularUnit_neighborhood_of_order_zero X x hx
    (a * L.rationalSectionCoordinate x) hzero
  let U := V ⊓ L.trivializingOpen x
  have hxU : x ∈ U := ⟨hxV, L.mem_trivializingOpen x⟩
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨U, inf_le_right, hxU,
    Units.map (X.presheaf.map (homOfLE (show U ≤ V from inf_le_left)).op).hom.toMonoidHom v, ?_⟩
  exact (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_restrict (show U ≤ V from inf_le_left) v).trans hv

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalUnitLocalSection (x : X) (U : X.Opens) (hU : U ≤ L.trivializingOpen x)
    (u : Γ(X, U)ˣ) : Γ(L.sheaf, U) := (L.sectionFrame x U hU).symm u.val

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalUnitLocalSection_coordinate (x : X) (U : X.Opens) (hU : U ≤ L.trivializingOpen x)
    (u : Γ(X, U)ˣ) : L.sectionFrame x U hU (L.rationalUnitLocalSection x U hU u) = u.val :=
  (L.sectionFrame x U hU).apply_symm_apply u.val

omit [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalUnitLocalSection_ne_zero (x : X) (U : X.Opens) [Nonempty U]
    (hU : U ≤ L.trivializingOpen x) (u : Γ(X, U)ˣ) : L.rationalUnitLocalSection x U hU u ≠ 0 := by
  intro h
  have he := congrArg (L.sectionFrame x U hU) h
  rw [L.rationalUnitLocalSection_coordinate x U hU u, map_zero] at he
  exact u.ne_zero he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
