import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur

/-! # Finite Conjugation -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization

noncomputable section

section

/-! An explicit symplectic inclusion at one finite prime, equal to the identity elsewhere. -/

open scoped Classical RestrictedProduct _root_.Matrix
open _root_.Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem finitePrimeEval_include_other (v w : HeightOneSpectrum ℤ) (hw : w ≠ v)
    (x : v.adicCompletion ℚ) : FiniteSchur.Realization.finitePrimeEval w (FiniteSchur.Realization.finitePrimeInclude v x) = 0 := by
  change RestrictedProduct.single (fun z : HeightOneSpectrum ℤ => z.adicCompletionIntegers ℚ) v x w = 0
  exact RestrictedProduct.single_eq_of_ne _ _ hw

variable {κ : Type*} [DecidableEq κ]

def finitePrimeMatrix (v : HeightOneSpectrum ℤ) (A : Matrix κ κ (v.adicCompletion ℚ)) : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i j => (1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j + FiniteSchur.Realization.finitePrimeInclude v (A i j - (1 : Matrix κ κ (v.adicCompletion ℚ)) i j)

theorem finitePrimeEval_matrix_one (w : HeightOneSpectrum ℤ) (i j : κ) :
    FiniteSchur.Realization.finitePrimeEval w ((1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j) = (1 : Matrix κ κ (w.adicCompletion ℚ)) i j := by
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem finitePrimeMatrix_eval_same (v : HeightOneSpectrum ℤ) (A : Matrix κ κ (v.adicCompletion ℚ)) :
    (finitePrimeMatrix v A).map (FiniteSchur.Realization.finitePrimeEval v) = A := by
  apply Matrix.ext
  intro i j
  change FiniteSchur.Realization.finitePrimeEval v ((1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j +
    FiniteSchur.Realization.finitePrimeInclude v (A i j - (1 : Matrix κ κ (v.adicCompletion ℚ)) i j)) = A i j
  rw [map_add, FiniteSchur.Realization.finitePrimeEval_include, finitePrimeEval_matrix_one]
  abel

theorem finitePrimeMatrix_eval_other (v w : HeightOneSpectrum ℤ) (hw : w ≠ v)
    (A : Matrix κ κ (v.adicCompletion ℚ)) :
    (finitePrimeMatrix v A).map (FiniteSchur.Realization.finitePrimeEval w) = 1 := by
  apply Matrix.ext
  intro i j
  change FiniteSchur.Realization.finitePrimeEval w ((1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j +
    FiniteSchur.Realization.finitePrimeInclude v (A i j - (1 : Matrix κ κ (v.adicCompletion ℚ)) i j)) = _
  rw [map_add, finitePrimeEval_include_other v w hw, add_zero, finitePrimeEval_matrix_one]

omit [DecidableEq κ] in
theorem finiteMatrix_ext {A B : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf}
    (h : ∀ w : HeightOneSpectrum ℤ, A.map (FiniteSchur.Realization.finitePrimeEval w) = B.map (FiniteSchur.Realization.finitePrimeEval w)) : A = B := by
  apply Matrix.ext
  intro i j
  apply DFunLike.ext
  intro w
  exact congrFun (congrFun (h w) i) j

theorem finitePrimeMatrix_one (v : HeightOneSpectrum ℤ) :
    finitePrimeMatrix v (1 : Matrix κ κ (v.adicCompletion ℚ)) = 1 := by
  apply Matrix.ext
  intro i j
  change (1 : Matrix κ κ Theta.PoissonAutomorphyNormalizationData.AQf) i j + FiniteSchur.Realization.finitePrimeInclude v
    ((1 : Matrix κ κ (v.adicCompletion ℚ)) i j - (1 : Matrix κ κ (v.adicCompletion ℚ)) i j) = _
  rw [sub_self, map_zero, add_zero]

variable [Fintype κ]

theorem finitePrimeMatrix_mul (v : HeightOneSpectrum ℤ) (A B : Matrix κ κ (v.adicCompletion ℚ)) :
    finitePrimeMatrix v (A * B) = finitePrimeMatrix v A * finitePrimeMatrix v B := by
  apply finiteMatrix_ext
  intro w
  rw [Matrix.map_mul]
  by_cases hw : w = v
  · subst w
    rw [finitePrimeMatrix_eval_same, finitePrimeMatrix_eval_same, finitePrimeMatrix_eval_same]
  · rw [finitePrimeMatrix_eval_other v w hw, finitePrimeMatrix_eval_other v w hw,
      finitePrimeMatrix_eval_other v w hw, Matrix.one_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finitePrimeMatrix_symplectic (v : HeightOneSpectrum ℤ)
    (g : Theta.PoissonAutomorphyNormalizationData.Sp ι (v.adicCompletion ℚ)) : finitePrimeMatrix v g.val ∈ Matrix.symplecticGroup ι Theta.PoissonAutomorphyNormalizationData.AQf := by
  apply SymplecticGroup.mem_iff'.mpr
  apply finiteMatrix_ext
  intro w
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_J]
  by_cases hw : w = v
  · subst w
    rw [finitePrimeMatrix_eval_same]
    exact SymplecticGroup.mem_iff'.mp g.property
  · rw [finitePrimeMatrix_eval_other v w hw, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

def finitePrimeSymplecticInclusion (v : HeightOneSpectrum ℤ) : Theta.PoissonAutomorphyNormalizationData.Sp ι (v.adicCompletion ℚ) →* Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun g := ⟨finitePrimeMatrix v g.val, finitePrimeMatrix_symplectic v g⟩
  map_one' := Subtype.ext (finitePrimeMatrix_one v)
  map_mul' g h := Subtype.ext (finitePrimeMatrix_mul v g.val h.val)

theorem finitePrimeSymplecticInclusion_projection (v : HeightOneSpectrum ℤ)
    (g : Theta.PoissonAutomorphyNormalizationData.Sp ι (v.adicCompletion ℚ)) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (finitePrimeSymplecticInclusion v g) = g :=
  Subtype.ext (finitePrimeMatrix_eval_same v g.val)

theorem mapSp_ringEquiv_cancel {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (g : Theta.PoissonAutomorphyNormalizationData.Sp ι A) : Theta.PoissonAutomorphyNormalizationData.mapSp e.symm.toRingHom (Theta.PoissonAutomorphyNormalizationData.mapSp e.toRingHom g) = g := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact e.symm_apply_apply _

def finitePadicSymplecticInclusion (q : ℕ) [Fact q.Prime] : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q] →* Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf :=
  (finitePrimeSymplecticInclusion (FiniteSchur.Realization.rationalPrime q)).comp (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom)

theorem finitePadicSymplecticInclusion_projection (q : ℕ) [Fact q.Prime] (g : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q]) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom (finitePadicSymplecticInclusion q g) = g := by
  have h := finitePrimeSymplecticInclusion_projection (FiniteSchur.Realization.rationalPrime q)
    (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom g)
  exact (congrArg (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.padicCoordinateEquiv q).symm.toRingHom) h).trans
    (mapSp_ringEquiv_cancel (FiniteSchur.Realization.padicCoordinateEquiv q).toRingEquiv g)

end

/-! Lifting and conjugating a local symplectic coordinate change in the actual finite cover. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mapSp_algebraMap {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι R) :
    Theta.PoissonAutomorphyNormalizationData.mapSp f.toRingHom (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap R A) γ) = Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap R B) γ := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact f.commutes (γ.val i j)

theorem rationalSymplectic_finite_projection (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ) =
      Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ :=
  mapSp_algebraMap (FiniteSchur.Realization.finitePadicProjection q) γ

theorem finiteSymplectic_conjugation_projection (S : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q]) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (finitePadicSymplecticInclusion q S * Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ Theta.PoissonAutomorphyNormalizationData.AQf) γ *
        (finitePadicSymplecticInclusion q S)⁻¹) =
      S * Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ * S⁻¹ := by
  rw [map_mul, map_mul, map_inv, finitePadicSymplecticInclusion_projection,
    rationalSymplectic_finite_projection]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem exists_finite_coordinate_lift (S : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q]) :
    ∃ s : MpF, D.finite.project s = finitePadicSymplecticInclusion q S :=
  D.finite.surjective (finitePadicSymplecticInclusion q S)

theorem finite_coordinate_conjugation_projection (S : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ_[q]) (s : MpF)
    (hs : D.finite.project s = finitePadicSymplecticInclusion q S) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom
      (D.finite.project (s * D.finiteLift γ * s⁻¹)) =
        S * Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℚ_[q]) γ * S⁻¹ := by
  rw [D.finite.project.map_mul, D.finite.project.map_mul, D.finite.project.map_inv,
    hs, D.finiteLift_covers]
  exact finiteSymplectic_conjugation_projection q S γ

theorem finite_coordinate_conjugation_action (s : MpF) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ)
    (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    D.finite.action (s * D.finiteLift γ * s⁻¹) (D.finite.action s f) =
      D.finite.action s (D.finiteAction γ f) := by
  rw [map_mul, map_mul]
  change D.finite.action s (D.finite.action (D.finiteLift γ)
    (D.finite.action s⁻¹ (D.finite.action s f))) = _
  change D.finite.action s (D.finite.action (D.finiteLift γ)
    ((D.finite.action s⁻¹ * D.finite.action s) f)) = _
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization
