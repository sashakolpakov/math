import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalCoefficient

/-! # Generic Coefficient Scalar -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: actual scalar multiplication of regular sections agrees with generic rational coefficients -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient_smul (x : X) (U : X.Opens) [Nonempty U]
    (hU : U ≤ L.trivializingOpen x) (r : Γ(X, U)) (s : Γ(L.sheaf, U)) :
    L.localRationalCoefficient x U hU (r • s) =
      X.germToFunctionField U r * L.localRationalCoefficient x U hU s := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [(L.sectionFrame x U hU).map_smul]
  change X.germToFunctionField U (r * L.sectionFrame x U hU s) / (L.rationalSectionCoordinate x).val = _
  rw [map_mul, mul_div_assoc]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.genericSectionCoefficient_smul (U : X.Opens) [Nonempty U]
    (r : Γ(X, U)) (s : Γ(L.sheaf, U)) :
    L.genericSectionCoefficient U (r • s) =
      X.germToFunctionField U r * L.genericSectionCoefficient U s := by
  let V := L.genericCoefficientDomain U
  have hVU : V ≤ U := inf_le_left
  have hr := L.sheaf.map_smul (homOfLE hVU) r s
  change L.localRationalCoefficient (genericPoint X) V inf_le_right
    (L.sheaf.presheaf.map (homOfLE hVU).op (r • s)) = _
  have hv := L.localRationalCoefficient_smul (genericPoint X) V inf_le_right
    (X.presheaf.map (homOfLE hVU).op r) (L.sheaf.presheaf.map (homOfLE hVU).op s)
  exact (congrArg (L.localRationalCoefficient (genericPoint X) V inf_le_right) hr).trans
    (hv.trans (congrArg (fun z => z * L.genericSectionCoefficient U s)
      (RationalBoundary.BundleCycles.RationalUnitRepresentative.germ_restrict hVU r)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
