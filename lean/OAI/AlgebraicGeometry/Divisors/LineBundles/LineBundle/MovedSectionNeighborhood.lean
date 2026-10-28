import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalUnitNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalSectionGluing

/-! # Moved Section Neighborhood -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: the moved rational section is an actual regular section near every avoided divisor point -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalUnitLocalSection_coefficient (a : X.functionFieldˣ) (x : X) (U : X.Opens)
    [Nonempty U] (hU : U ≤ L.trivializingOpen x) (u : Γ(X, U)ˣ)
    (hu : FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm U u = a * L.rationalSectionCoordinate x) :
    L.localRationalCoefficient x U hU (L.rationalUnitLocalSection x U hU u) = a.val := by
  unfold LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.localRationalCoefficient
  rw [L.rationalUnitLocalSection_coordinate x U hU u]
  have he := congrArg (fun v : X.functionFieldˣ => v.val) hu
  change X.germToFunctionField U u.val = a.val * (L.rationalSectionCoordinate x).val at he
  rw [he, mul_div_cancel_right₀ _ (L.rationalSectionCoordinate x).ne_zero]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_regularSection_near_avoided_points {ι : Type}
    (a : X.functionFieldˣ) (x : ι → X) (hx : ∀ i, coheight (x i) = 1)
    [∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))]
    (ha : ∀ i, L.rationalSectionPointDivisorWithCoefficient a (x i) = 0) :
    ∃ (U : ι → X.Opens) (hU : ∀ i, U i ≤ L.trivializingOpen (x i))
      (hxU : ∀ i, x i ∈ U i) (u : ∀ i, Γ(X, U i)ˣ) (t : Γ(L.sheaf, iSup U)),
      ∀ i, L.sheaf.presheaf.map (homOfLE (le_iSup U i)).op t =
        L.rationalUnitLocalSection (x i) (U i) (hU i) (u i) ∧
        letI : Nonempty (U i) := ⟨⟨x i, hxU i⟩⟩
        FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (U i) (u i) = a * L.rationalSectionCoordinate (x i) := by
  classical
  choose U hU hxU u hu using fun i => L.exists_rationalSection_unit_neighborhood a (x i) (hx i) (ha i)
  let : ∀ i, Nonempty (U i) := fun i => ⟨⟨x i, hxU i⟩⟩
  let s := fun i => L.rationalUnitLocalSection (x i) (U i) (hU i) (u i)
  have hs : ∀ i, L.localRationalCoefficient (x i) (U i) (hU i) (s i) = a.val :=
    fun i => L.rationalUnitLocalSection_coefficient a (x i) (U i) (hU i) (u i) (hu i)
  obtain ⟨t, ht, _⟩ := L.existsUnique_gluedRationalSection x U hU s a.val hs
  exact ⟨U, hU, hxU, u, t, fun i => ⟨ht i, hu i⟩⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
