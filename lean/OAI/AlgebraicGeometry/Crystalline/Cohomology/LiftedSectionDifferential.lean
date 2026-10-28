import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedTermLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionDifferential
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CoefficientSheafNaturality

/-! # Lifted Section Differential -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedSectionDifferential.CrystallineLiftedSectionDifferential

noncomputable section

/-! # The actual sheaf section equivalence preserves the PD differential -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "Native" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "KS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionDifferential.CrystallineFrameSectionDifferential.differentialMap p k B σ r hr hbase

omit [LinearOrder σ] in
theorem inverse_naturality (n : ℕ) :
    Functor.whiskerRight ((K).d n (n + 1)) E ≫ (e (n + 1)).inv =
      (e n).inv ≫ ((KS).d n (n + 1)).hom := by
  have h := CoefficientSheafNaturality.CrystallineCoefficientSheafNaturality.naturality p k X ((K).X n) ((K).X (n + 1))
    (CrystallineFrame.FormsSheaf.CrystallineFrameFormsSheaf.term_isSheaf p k B σ a n)
    (CrystallineFrame.FormsSheaf.CrystallineFrameFormsSheaf.term_isSheaf p k B σ a (n + 1)) ((K).d n (n + 1))
  change (e n).hom ≫ Functor.whiskerRight ((K).d n (n + 1)) E =
    ((KS).d n (n + 1)).hom ≫ (e (n + 1)).hom at h
  apply (Iso.comp_inv_eq (e (n + 1))).mpr
  exact ((e n).inv_hom_id_assoc _).symm.trans
    ((congrArg (fun f => (e n).inv ≫ f) h).trans (Category.assoc _ _ _).symm)

omit [LinearOrder σ] in
theorem differential (n : ℕ) (Q : Nativeᵒᵖ) :
    (E).map (d n) ≫ (LiftedTermLimit.CrystallineLiftedTermLimit.cone p k B σ r hr hbase (n + 1)).π.app Q =
      (LiftedTermLimit.CrystallineLiftedTermLimit.cone p k B σ r hr hbase n).π.app Q ≫
        (((KS).d n (n + 1)).hom.app Q) := by
  have hraw := congrArg (fun f => (E).map f)
    (CrystallineFrame.SectionDifferential.CrystallineFrameSectionDifferential.differential p k B σ r hr hbase n Q)
  simp only [Functor.map_comp] at hraw
  have hiso := congrArg (fun f => f.app Q) (inverse_naturality p k B σ r n)
  change (E).map (((K).d n (n + 1)).app Q) ≫ (e (n + 1)).inv.app Q =
    (e n).inv.app Q ≫ ((KS).d n (n + 1)).hom.app Q at hiso
  change (E).map (d n) ≫
    ((E).map ((CrystallineFrame.TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase (n + 1)).π.app Q) ≫
      (e (n + 1)).inv.app Q) =
        ((E).map ((CrystallineFrame.TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase n).π.app Q) ≫
          (e n).inv.app Q) ≫ ((KS).d n (n + 1)).hom.app Q
  rw [← Category.assoc, hraw, Category.assoc, hiso, ← Category.assoc]

theorem sectionsEquiv_differential (n : ℕ)
    (s : (Functor.const Nativeᵒᵖ).obj (ModuleCat.of R R) ⟶ ((KS).X n).obj) :
    LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase (n + 1)
        (s ≫ ((KS).d n (n + 1)).hom) =
      (E).map (d n) (LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase n s) :=
  Module.ConeSections.ModuleConeSections.naturality R
    (LiftedTermLimit.CrystallineLiftedTermLimit.cone p k B σ r hr hbase n)
    (LiftedTermLimit.CrystallineLiftedTermLimit.isLimit p k B σ r hr hbase n)
    (LiftedTermLimit.CrystallineLiftedTermLimit.cone p k B σ r hr hbase (n + 1))
    (LiftedTermLimit.CrystallineLiftedTermLimit.isLimit p k B σ r hr hbase (n + 1))
    (((KS).d n (n + 1)).hom) ((E).map (d n)) (differential p k B σ r hr hbase n) s

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedSectionDifferential.CrystallineLiftedSectionDifferential
