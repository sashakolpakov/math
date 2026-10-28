import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.TermLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech

/-! # Lifted Term Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedTermLimit.CrystallineLiftedTermLimit

noncomputable section

/-!
# Sections of the actual sheafified frame terms

The coefficient-universe lift preserves the native term limits because
the framed limits are computed on the countable original tower. The
canonical sheafification isomorphism gives a limit cone for the actual
presheaf underlying every frame sheaf, with the prescribed coefficients.
-/

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
local notation "Framed" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.frame p k B σ a
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.forget p k B σ a
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase
local notation "P" => Functor.op U ⋙ OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.functions p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "KS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k

local instance frameFinal : (G).Final :=
  Functor.final_of_adjunction (CrystallineFrame.Adjunction.CrystallineFrameAdjunction.adjunction p k B σ a)

local instance coefficientCountable : PreservesLimitsOfShape ℕᵒᵖ E := by
  unfold PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift
  have : PreservesLimitsOfSize.{u, u} (ModuleCat.uliftFunctor.{u + 1, u} W) := inferInstance
  have : PreservesLimitsOfSize.{0, 0} (ModuleCat.uliftFunctor.{u + 1, u} W) :=
    preservesSmallestLimits_of_preservesLimits _
  have : PreservesLimitsOfShape ℕᵒᵖ
      (ModuleCat.restrictScalars.{u + 1} (ULift.ringEquiv : R ≃+* W).toRingHom) :=
    ⟨fun {L} => ModuleCat.preservesLimit_restrictScalars _ L⟩
  exact comp_preservesLimitsOfShape _ _

include hr hbase in
omit [LinearOrder σ] in
theorem preservesTermLimit (n : ℕ) : PreservesLimit ((K).X n) E := by
  let : PreservesLimitsOfShape Framedᵒᵖ E :=
    Functor.Initial.preservesLimitsOfShape_of_initial (Tower).op E
  exact inferInstanceAs (PreservesLimit
    ((G).op ⋙ (P ⋙ Finite.TensorSheaf.FiniteTensorSheaf.tensor W (⋀[W]^n (σ →₀ W)))) E)

def cone (n : ℕ) : Cone (((KS).X n).obj) :=
  (Cone.postcompose (CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a n).inv).obj
    ((E).mapCone (CrystallineFrame.TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase n))

def isLimit (n : ℕ) : IsLimit (cone p k B σ r hr hbase n) := by
  let : PreservesLimit ((K).X n) E := preservesTermLimit p k B σ r hr hbase n
  exact (IsLimit.postcomposeInvEquiv (CrystallineFrame.SheafCech.CrystallineFrameSheafCech.sectionPresheafIso p k B σ a n) _).symm
    (isLimitOfPreserves E (CrystallineFrame.TermLimit.CrystallineFrameTermLimit.isLimit p k B σ r hr hbase n))

def sectionsEquiv (n : ℕ) :
    ((Functor.const Nativeᵒᵖ).obj (ModuleCat.of R R) ⟶ ((KS).X n).obj) ≃ₗ[R]
      (E).obj (CrystallineFrame.TermLimit.CrystallineFrameTermLimit.cone p k B σ r hr hbase n).pt :=
  Module.ConeSections.ModuleConeSections.sectionsEquiv R (cone p k B σ r hr hbase n) (isLimit p k B σ r hr hbase n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedTermLimit.CrystallineLiftedTermLimit
