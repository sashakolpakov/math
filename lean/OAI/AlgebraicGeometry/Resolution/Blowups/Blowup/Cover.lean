import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Charts
import Mathlib.AlgebraicGeometry.Properties

/-! # Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Cover.Construction

noncomputable section

/-! Reducedness and integrality of the actual affine blowup for Blowups. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Blowup charts over a reduced ring are reduced, by their proved embedding
into a localization of that ring. -/
instance blowupChart_isReduced [_root_.IsReduced R] (a : I) :
    _root_.IsReduced (Charts.Construction.blowupChart I a) :=
  isReduced_of_injective (Charts.Construction.blowupChartToLocalization I a)
    (Charts.Construction.blowupChartToLocalization_injective I a)

/-- The affine open cover given by the degree-one Rees generators. -/
def affineBlowupAffineCover : (ReesGrading.Construction.affineBlowup I).AffineOpenCover where
  I₀ := I
  X a := .of (Charts.Construction.blowupChart I a)
  f a := Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((Charts.Construction.affineBlowup_chart_cover I).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (ReesGrading.Construction.reesGrade I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((Charts.Construction.affineBlowup_chart_cover I).ge (Set.mem_univ x))).choose_spec

/-- Blowup preserves reducedness on affine schemes. -/
instance affineBlowup_isReduced [_root_.IsReduced R] :
    AlgebraicGeometry.IsReduced (ReesGrading.Construction.affineBlowup I) := by
  let 𝒰 := (affineBlowupAffineCover I).openCover
  let : ∀ i : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X i) := by
    intro i
    change AlgebraicGeometry.IsReduced (Spec (.of (Charts.Construction.blowupChart I i)))
    apply (AlgebraicGeometry.affine_isReduced_iff (.of (Charts.Construction.blowupChart I i))).mpr
    exact blowupChart_isReduced I i
  exact AlgebraicGeometry.IsReduced.of_openCover (ReesGrading.Construction.affineBlowup I) 𝒰

/-- The zero homogeneous prime of the Rees algebra is a point of its Proj
when the base is a domain and the center ideal is nonzero. -/
def affineBlowupGenericPoint [IsDomain R] (hI : I ≠ ⊥) :
    ProjectiveSpectrum (ReesGrading.Construction.reesGrade I) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    infer_instance
  not_irrelevant_le := by
    intro h
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff I).mp hI
    have hz : Charts.Construction.reesGenerator I ⟨a, ha⟩ ∈ (⊥ : HomogeneousIdeal (ReesGrading.Construction.reesGrade I)) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem (ReesGrading.Construction.reesGrade I) (by decide)
        (Charts.Construction.reesGenerator_mem I ⟨a, ha⟩))
    have hzero : Charts.Construction.reesGenerator I ⟨a, ha⟩ = 0 := by
      change Charts.Construction.reesGenerator I ⟨a, ha⟩ ∈ (⊥ : HomogeneousIdeal (ReesGrading.Construction.reesGrade I)).toIdeal at hz
      rw [HomogeneousIdeal.toIdeal_bot] at hz
      exact Ideal.mem_bot.mp hz
    apply ha0
    have hc := congrArg (fun p : reesAlgebra I => p.val.coeff 1) hzero
    simpa [Charts.Construction.reesGenerator] using hc

/-- The constructed zero prime is dense in the affine blowup. -/
theorem affineBlowupGenericPoint_closure [IsDomain R] (hI : I ≠ ⊥) :
    closure ({affineBlowupGenericPoint I hI} : Set (ProjectiveSpectrum (ReesGrading.Construction.reesGrade I))) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure (ReesGrading.Construction.reesGrade I)
    (affineBlowupGenericPoint I hI) x).mp
  change (⊥ : HomogeneousIdeal (ReesGrading.Construction.reesGrade I)) ≤ x.asHomogeneousIdeal
  exact bot_le

/-- The blowup of a nonzero ideal in a domain is irreducible. -/
theorem affineBlowup_irreducible [IsDomain R] (hI : I ≠ ⊥) :
    IrreducibleSpace (ReesGrading.Construction.affineBlowup I) := by
  apply (irreducibleSpace_def (ReesGrading.Construction.affineBlowup I)).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum (ReesGrading.Construction.reesGrade I)))
  rw [← affineBlowupGenericPoint_closure I hI]
  exact (isIrreducible_singleton : IsIrreducible {affineBlowupGenericPoint I hI}).closure

/-- The blowup of a nonzero ideal in an affine integral scheme is integral. -/
theorem affineBlowup_integral [IsDomain R] (hI : I ≠ ⊥) :
    AlgebraicGeometry.IsIntegral (ReesGrading.Construction.affineBlowup I) := by
  let : IrreducibleSpace (ReesGrading.Construction.affineBlowup I) := affineBlowup_irreducible I hI
  exact isIntegral_of_irreducibleSpace_of_isReduced (ReesGrading.Construction.affineBlowup I)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Cover.Construction
