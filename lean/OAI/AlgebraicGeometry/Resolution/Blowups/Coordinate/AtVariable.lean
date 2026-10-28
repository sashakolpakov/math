import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialEtale
import Mathlib.Logic.Equiv.Option

/-! # At Variable -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.AtVariable.Construction

noncomputable section

/-! Étale coordinate neighborhoods using any chosen nonzero partial derivative. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry

variable {σ K : Type*} [Field K]

/-- Separate the chosen variable from the remaining variables. -/
def separateVariableEquiv (i : σ) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial (Option {j : σ // j ≠ i}) K := by
  classical
  exact MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe i).symm

theorem separateVariableEquiv_X_self (i : σ) :
    separateVariableEquiv (K := K) i (X i) = X none := by
  classical
  simp [separateVariableEquiv]

theorem separateVariableEquiv_X_ne (i j : σ) (hji : j ≠ i) :
    separateVariableEquiv (K := K) i (X j) = X (some ⟨j, hji⟩) := by
  classical
  simp [separateVariableEquiv, Equiv.optionSubtypeNe_symm_of_ne hji]

theorem separateVariableEquiv_pderiv (i : σ) (q : MvPolynomial σ K) :
    pderiv none (separateVariableEquiv i q) = separateVariableEquiv i (pderiv i q) := by
  classical
  simpa only [separateVariableEquiv, renameEquiv_apply, Equiv.optionSubtypeNe_symm_self] using
    pderiv_rename (Equiv.optionSubtypeNe i).symm.injective i q

theorem separateVariableEquiv_eval (i : σ) (a : σ → K) (q : MvPolynomial σ K) :
    eval (fun o => Option.elim o (a i) (fun j => a j.val)) (separateVariableEquiv i q) = eval a q := by
  classical
  have he : (fun o => Option.elim o (a i) (fun j : {j : σ // j ≠ i} => a j.val)) =
      a ∘ Equiv.optionSubtypeNe i := by
    funext o
    cases o <;> rfl
  rw [he]
  rw [separateVariableEquiv, renameEquiv_apply, eval_rename]
  have hc : (a ∘ Equiv.optionSubtypeNe i) ∘ (Equiv.optionSubtypeNe i).symm = a := by
    funext x
    exact congrArg a ((Equiv.optionSubtypeNe i).apply_symm_apply x)
  rw [hc]

/-- The actual coordinate chart associated to the `i`th partial derivative of `q`. -/
abbrev coordinateChartAtVariable (q : MvPolynomial σ K) (i : σ) :=
  PolynomialEtale.Construction.localPolynomialCoordinateChart (separateVariableEquiv i q)

def coordinateAmbientMapAtVariable (q : MvPolynomial σ K) (i : σ) :
    MvPolynomial σ K →+* coordinateChartAtVariable q i :=
  (PolynomialEtale.Construction.localPolynomialAmbientMap (separateVariableEquiv i q)).comp (separateVariableEquiv i).toRingHom

def coordinateReplacementMapAtVariable (q : MvPolynomial σ K) (i : σ) :
    MvPolynomial σ K →+* coordinateChartAtVariable q i :=
  (PolynomialEtale.Construction.localPolynomialCoordinateMap (separateVariableEquiv i q)).comp (separateVariableEquiv i).toRingHom

/-- The selected coordinate becomes exactly the hypersurface equation. -/
theorem coordinateReplacementMapAtVariable_self (q : MvPolynomial σ K) (i : σ) :
    coordinateReplacementMapAtVariable q i (X i) = coordinateAmbientMapAtVariable q i q := by
  change PolynomialEtale.Construction.localPolynomialCoordinateMap (separateVariableEquiv i q) (separateVariableEquiv i (X i)) =
    PolynomialEtale.Construction.localPolynomialAmbientMap (separateVariableEquiv i q) (separateVariableEquiv i q)
  rw [separateVariableEquiv_X_self, PolynomialEtale.Construction.localPolynomialCoordinateMap_none]

/-- The remaining original coordinates are retained. -/
theorem coordinateReplacementMapAtVariable_ne (q : MvPolynomial σ K) (i j : σ) (hji : j ≠ i) :
    coordinateReplacementMapAtVariable q i (X j) = coordinateAmbientMapAtVariable q i (X j) := by
  change PolynomialEtale.Construction.localPolynomialCoordinateMap (separateVariableEquiv i q) (separateVariableEquiv i (X j)) =
    PolynomialEtale.Construction.localPolynomialAmbientMap (separateVariableEquiv i q) (separateVariableEquiv i (X j))
  rw [separateVariableEquiv_X_ne i j hji, PolynomialEtale.Construction.localPolynomialCoordinateMap_some]

/-- The chart is an open subscheme of the original ambient affine space. -/
theorem coordinateAmbientMapAtVariable_isOpenImmersion (q : MvPolynomial σ K) (i : σ) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (coordinateAmbientMapAtVariable q i))) := by
  let e := (separateVariableEquiv (K := K) i).toRingEquiv.toCommRingCatIso
  let f := CommRingCat.ofHom (PolynomialEtale.Construction.localPolynomialAmbientMap (separateVariableEquiv i q))
  let : IsOpenImmersion (Spec.map f) := PolynomialEtale.Construction.localPolynomialAmbientMap_isOpenImmersion _
  change IsOpenImmersion (Spec.map (e.hom ≫ f))
  rw [Spec.map_comp]
  infer_instance

/-- The replacement of the selected coordinate by `q` is étale. -/
theorem coordinateReplacementMapAtVariable_etale (q : MvPolynomial σ K) (i : σ) :
    Etale (Spec.map (CommRingCat.ofHom (coordinateReplacementMapAtVariable q i))) := by
  let e := (separateVariableEquiv (K := K) i).toRingEquiv.toCommRingCatIso
  let f := CommRingCat.ofHom (PolynomialEtale.Construction.localPolynomialCoordinateMap (separateVariableEquiv i q))
  let : Etale (Spec.map f) := PolynomialEtale.Construction.localPolynomialCoordinateMap_etale _
  change Etale (Spec.map (e.hom ≫ f))
  rw [Spec.map_comp]
  infer_instance

/-- A point with nonzero chosen partial derivative lies on this coordinate
neighborhood, with every original polynomial coordinate preserved. -/
theorem coordinateChartAtVariable_has_point (q : MvPolynomial σ K) (i : σ) (a : σ → K)
    (ha : eval a (pderiv i q) ≠ 0) :
    ∃ e : coordinateChartAtVariable q i →+* K,
      ∀ r : MvPolynomial σ K, e (coordinateAmbientMapAtVariable q i r) = eval a r := by
  let a' : Option {j : σ // j ≠ i} → K := fun o => Option.elim o (a i) (fun j => a j.val)
  have ha' : eval a' (pderiv none (separateVariableEquiv i q)) ≠ 0 := by
    rw [separateVariableEquiv_pderiv]
    exact (separateVariableEquiv_eval i a (pderiv i q)) ▸ ha
  obtain ⟨e, he⟩ := PolynomialEtale.Construction.localPolynomialCoordinateChart_has_point (separateVariableEquiv i q) a' ha'
  refine ⟨e, ?_⟩
  intro r
  rw [coordinateAmbientMapAtVariable, RingHom.comp_apply, he]
  exact separateVariableEquiv_eval i a r

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.AtVariable.Construction
