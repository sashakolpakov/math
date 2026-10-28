import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CenterBoundaryColon
import OAI.AlgebraicGeometry.Resolution.Blowups.ComaximalFactorUniqueness
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelSums

/-! # Binary Incidence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

section

/-! Canonical containing and avoiding parts of a smooth center, characterized by native ideal quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def Boundary.BinaryIncidence.Construction.boundaryContainingFaces {β : Type} [Fintype β] (j : β) : Finset (Finset β) := by
  classical
  exact Finset.univ.filter (fun F => j ∈ F)

variable {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] [DecidableEq β] (D : β → X.IdealSheafData)

def Boundary.BinaryIncidence.Construction.boundaryContainingCenter (j : β) : X.IdealSheafData :=
  Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D (Boundary.BinaryIncidence.Construction.boundaryContainingFaces j)

def Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter (j : β) : X.IdealSheafData :=
  Boundary.IncidenceCenter.Construction.selectedIncidenceCenter f I D (Boundary.BinaryIncidence.Construction.boundaryContainingFaces j)ᶜ

theorem Boundary.BinaryIncidence.Construction.binaryBoundaryIncidence_factorization (j : β) :
    I = Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j * Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j :=
  Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_factorization f I D _

theorem Boundary.BinaryIncidence.Construction.binaryBoundaryIncidence_comaximal (j : β) :
    Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j ⊔ Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j = ⊤ :=
  Boundary.IncidenceCenter.Construction.selectedIncidenceCenter_disjoint f I D _ _ disjoint_compl_right

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundaryAvoidingCenter_eq_colon [IsLocallyNoetherian X]
    (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D) (j : β) :
    Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j = NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon I (D j) := by
  classical
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover A.opens A.cover).openCover
  intro i
  change A.indices at i
  have he : (Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).ideal (A.opens i) =
      (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon I (D j)).ideal (A.opens i) := by
    rw [Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter, A.selectedIncidence_ideal f I D, A.boundary_colon_ideal j i]
    simp only [Boundary.BinaryIncidence.Construction.boundaryContainingFaces, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j ∈ A.divided i <;> simp only [hj, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
  change (Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).comap (A.opens i).2.fromSpec =
    (NoetherianIdealSheafColon.Construction.noetherianIdealSheafColon I (D j)).comap (A.opens i).2.fromSpec
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, he]

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundaryAvoidingCenter_comap_flat
    [IsLocallyNoetherian X] (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    {Y : Scheme} [IsLocallyNoetherian Y] (q : Y ⟶ X) [Flat q] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth ((I.comap q).subschemeι ≫ g)] [Fintype (irreducibleComponents (I.comap q).subscheme)]
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g (I.comap q) (fun l => (D l).comap q)) (j : β) :
    (Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).comap q =
      Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter g (I.comap q) (fun l => (D l).comap q) j := by
  rw [A.boundaryAvoidingCenter_eq_colon f I D j, A.boundary_colon_comap_flat j q,
    B.boundaryAvoidingCenter_eq_colon]

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundaryContainingCenter_comap_flat
    [IsLocallyNoetherian X] (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    {Y : Scheme} [IsLocallyNoetherian Y] (q : Y ⟶ X) [Flat q] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth ((I.comap q).subschemeι ≫ g)] [Fintype (irreducibleComponents (I.comap q).subscheme)]
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g (I.comap q) (fun l => (D l).comap q)) (j : β) :
    (Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j).comap q =
      Boundary.BinaryIncidence.Construction.boundaryContainingCenter g (I.comap q) (fun l => (D l).comap q) j := by
  let L := Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter g (I.comap q) (fun l => (D l).comap q) j
  have he := A.boundaryAvoidingCenter_comap_flat f I D q g B j
  change (Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).comap q = L at he
  apply ComaximalFactorUniqueness.Construction.idealSheaf_comaximal_factor_unique _ _ L
  · rw [← he, ← Scheme.IdealSheafData.comap_sup, Boundary.BinaryIncidence.Construction.binaryBoundaryIncidence_comaximal,
      Scheme.IdealSheafData.comap_top]
  · exact Boundary.BinaryIncidence.Construction.binaryBoundaryIncidence_comaximal g (I.comap q) (fun l => (D l).comap q) j
  · rw [← Boundary.BinaryIncidence.Construction.binaryBoundaryIncidence_factorization, ← he, ← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_mul,
      ← Boundary.BinaryIncidence.Construction.binaryBoundaryIncidence_factorization]

end

/-! Every canonical incidence group commutes with flat restriction between smooth boundary-center pairs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] [Fintype (irreducibleComponents I.subscheme)]
    {β : Type} [Fintype β] [DecidableEq β] (D : β → X.IdealSheafData) (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)

omit [IsLocallyNoetherian X] in
theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundaryContainingCenter_ideal (j : β) (i : A.indices) :
    (Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j).ideal (A.opens i) =
      if j ∈ A.divided i then I.ideal (A.opens i) else ⊤ := by
  rw [Boundary.BinaryIncidence.Construction.boundaryContainingCenter, A.selectedIncidence_ideal f I D]
  simp only [Boundary.BinaryIncidence.Construction.boundaryContainingFaces, Finset.mem_filter, Finset.mem_univ, true_and]

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.boundaryAvoidingCenter_ideal (j : β) (i : A.indices) :
    (Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).ideal (A.opens i) =
      if j ∈ A.divided i then ⊤ else I.ideal (A.opens i) := by
  rw [A.boundaryAvoidingCenter_eq_colon f I D j, A.boundary_colon_ideal j i]

include A in
theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.incidenceCenter_binary_formula (F : Finset β) :
    Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F = I ⊔ ⨆ j : β,
      if j ∈ F then Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j else Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j := by
  classical
  apply IdealSheaf.EqualityGluing.Construction.idealSheaf_eq_of_openCover _ _ (Global.MonomialBoundaryAtlas.Construction.chosenAffineSpecCover A.opens A.cover).openCover
  intro i
  change A.indices at i
  have he : (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).ideal (A.opens i) =
      (I ⊔ ⨆ j : β, if j ∈ F then Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j else Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).ideal (A.opens i) := by
    rw [A.incidenceCenter_ideal_formula f I D F i,
      Scheme.IdealSheafData.ideal_sup, Scheme.IdealSheafData.ideal_iSup]
    rw [Pi.sup_apply, iSup_apply]
    change (if A.divided i = F then I.ideal (A.opens i) else ⊤) = I.ideal (A.opens i) ⊔
      ⨆ j : β, (if j ∈ F then Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j else Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).ideal (A.opens i)
    by_cases hF : A.divided i = F
    · rw [ite_eq_left hF]
      apply le_antisymm le_sup_left
      apply sup_le le_rfl
      apply iSup_le
      intro j
      by_cases hj : j ∈ F
      · rw [ite_eq_left hj, A.boundaryContainingCenter_ideal f I D j i, hF, ite_eq_left hj]
      · rw [ite_eq_right hj, A.boundaryAvoidingCenter_ideal f I D j i, hF, ite_eq_right hj]
    · rw [ite_eq_right hF]
      have hex : ∃ j : β, ¬ (j ∈ A.divided i ↔ j ∈ F) := by
        by_contra! hn
        exact hF (Finset.ext hn)
      obtain ⟨j, hj⟩ := hex
      apply (top_le_iff.mp ?_).symm
      apply (le_iSup_of_le j ?_).trans le_sup_right
      by_cases hjF : j ∈ F
      · have hjA : j ∉ A.divided i := by tauto
        rw [ite_eq_left hjF, A.boundaryContainingCenter_ideal f I D j i, ite_eq_right hjA]
      · have hjA : j ∈ A.divided i := by tauto
        rw [ite_eq_right hjF, A.boundaryAvoidingCenter_ideal f I D j i, ite_eq_left hjA]
  change (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).comap (A.opens i).2.fromSpec =
    (I ⊔ ⨆ j : β, if j ∈ F then Boundary.BinaryIncidence.Construction.boundaryContainingCenter f I D j else Boundary.BinaryIncidence.Construction.boundaryAvoidingCenter f I D j).comap (A.opens i).2.fromSpec
  rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel, he]

include A in
theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.incidenceCenter_comap_flat
    {Y : Scheme} [IsLocallyNoetherian Y] (q : Y ⟶ X) [Flat q] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth ((I.comap q).subschemeι ≫ g)] [Fintype (irreducibleComponents (I.comap q).subscheme)]
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g (I.comap q) (fun l => (D l).comap q)) (F : Finset β) :
    (Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter f I D F).comap q =
      Boundary.IncidenceCenter.Construction.boundaryIncidenceCenter g (I.comap q) (fun l => (D l).comap q) F := by
  rw [A.incidenceCenter_binary_formula f I D F, Scheme.IdealSheafData.comap_sup,
    Affine.KernelSums.Construction.idealSheaf_comap_iSup, B.incidenceCenter_binary_formula]
  congr 1
  apply iSup_congr
  intro j
  by_cases hj : j ∈ F
  · rw [ite_eq_left hj, ite_eq_left hj]
    exact A.boundaryContainingCenter_comap_flat f I D q g B j
  · rw [ite_eq_right hj, ite_eq_right hj]
    exact A.boundaryAvoidingCenter_comap_flat f I D q g B j

end

end OAI.AlgebraicGeometry.Resolution.Blowups
