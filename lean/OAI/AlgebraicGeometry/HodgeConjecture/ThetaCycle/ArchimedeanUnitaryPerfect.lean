import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CompactThreePerfect
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallPerfect
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.UnitaryBasisCoordinates
import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Archimedean Unitary Perfect -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ArchimedeanUnitaryPerfect.CM

noncomputable section

/-! Perfectness in the actual native completion coordinates at every
real place, and for their finite archimedean product. -/

open scoped _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

theorem perfect_of_group_equiv {G T : Type*} [Group G] [Group T]
    (e : G ≃* T) (hT : commutator T = ⊤) : commutator G = ⊤ := by
  have : Group.IsPerfect T := ⟨hT⟩
  have : Group.IsPerfect G := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.commutator_eq_top

theorem finite_product_perfect {I : Type*} [Finite I] (G : I → Type*) [∀ i, Group (G i)]
    (hG : ∀ i, commutator (G i) = ⊤) : commutator (∀ i, G i) = ⊤ := by
  have h := Subgroup.commutator_pi_pi_of_finite (fun i => (⊤ : Subgroup (G i)))
    (fun i => (⊤ : Subgroup (G i)))
  simpa only [Subgroup.pi_top, ← commutator_def, hG] using h

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

theorem native_enumerated_real_unitary_perfect (v : Fin A.places) :
    commutator (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))) = ⊤ := by
  let M : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.diagonal (fun i => if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1)
  have hM : commutator (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU M) = ⊤ := by
    by_cases hv : v = A.distinguished
    · have he : M = RepresentationTheory.Theta.Adelic.BallNatural.standardForm.val := by
        apply Matrix.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [M, hv, RepresentationTheory.Theta.Adelic.BallNatural.standardForm]
      rw [he]
      exact BallPerfect.CM.ball_group_commutator_eq_top
    · have he : M = 1 := by simp [M, hv]
      rw [he]
      exact CompactThreePerfect.CM.compact_three_commutator_eq_top
  let e := UnitaryBasisCoordinates.CM.specialUnitaryFieldEquiv (A.complex v) (A.complex_star v)
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))
  let b := UnitaryBasisCoordinates.CM.specialUnitaryBasisEquiv
    ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))).map (A.complex v).toRingHom)
    M (A.basisV v) (A.formV v)
  exact perfect_of_group_equiv (e.trans b) hM

include A in
theorem native_real_unitary_perfect (v : NumberField.InfinitePlace F) :
    commutator (RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl v))) = ⊤ := by
  obtain ⟨i, rfl⟩ := A.enumerate.surjective v
  exact native_enumerated_real_unitary_perfect A i

include A in
theorem native_archimedean_unitary_perfect : commutator (RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) = ⊤ :=
  finite_product_perfect _ (native_real_unitary_perfect A)

include A in
theorem native_archimedean_character_eq_one {T : Type*} [CommGroup T]
    (χ : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H →* T) (g : RepresentationTheory.Theta.Adelic.RationalSU.ArchimedeanSU F H) : χ g = 1 := by
  apply Abelianization.commutator_subset_ker χ
  rw [native_archimedean_unitary_perfect A]
  trivial

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ArchimedeanUnitaryPerfect.CM
