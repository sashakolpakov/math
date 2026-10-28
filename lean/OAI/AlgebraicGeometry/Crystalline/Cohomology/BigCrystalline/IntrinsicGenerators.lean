import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafificationRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafCech

/-! # Intrinsic Generators -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators

noncomputable section

/-! # Actual big frame sheaf sections have unique generators at native objects -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "Big" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology
  (p := p) (B := W) (J := I) (δ := γ) (f := bX)
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := γ) (base := bX) a
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution.BigCrystallineFrameSheafResolution.complex p W B I γ bX a

def presheaf (n : ℕ) : Bigᵒᵖ ⥤ ModuleCat.{u + 1} R := (K).X n ⋙ E

def generator (n : ℕ) : presheaf p k B σ a n ⟶ ((S).X n).obj :=
  toSheafify U (presheaf p k B σ a n)

theorem restriction_isSheaf (n : ℕ) :
    Presheaf.IsSheaf T ((ι).op ⋙ presheaf p k B σ a n) := by
  let e : (ι).op ⋙ presheaf p k B σ a n ≅ (L).X n ⋙ E :=
    isoWhiskerRight ((HomologicalComplex.eval _ (.up ℕ) n).mapIso
      (IntrinsicResolution.BigCrystallineIntrinsicResolution.iso p k B σ a)) E
  exact (Presheaf.isSheaf_of_iso_iff e).mpr
    (CoefficientSheaf.CrystallineCoefficientSheaf.isSheaf p k X ((L).X n)
      (CrystallineFrame.FormsSheaf.CrystallineFrameFormsSheaf.term_isSheaf p k B σ a n))

instance generator_isIso (n : ℕ) (Q : C) :
    IsIso ((generator p k B σ a n).app (op ((ι).obj Q))) :=
  SheafificationRestriction.SheafificationRestrictionGenerators.component_isIso T U ι
    (presheaf p k B σ a n) (restriction_isSheaf p k B σ a n) Q

def representative (n : ℕ) (Q : C) (x : ((S).X n).obj.obj (op ((ι).obj Q))) :
    (presheaf p k B σ a n).obj (op ((ι).obj Q)) :=
  (inv ((generator p k B σ a n).app (op ((ι).obj Q)))).hom x

theorem generator_representative (n : ℕ) (Q : C)
    (x : ((S).X n).obj.obj (op ((ι).obj Q))) :
    ((generator p k B σ a n).app (op ((ι).obj Q))).hom
      (representative p k B σ a n Q x) = x :=
  ConcreteCategory.congr_hom (IsIso.inv_hom_id ((generator p k B σ a n).app (op ((ι).obj Q)))) x

theorem section_at_map (n : ℕ) (Q : C) (P : Big) (f : P ⟶ (ι).obj Q)
    (s : (Functor.const Bigᵒᵖ).obj (ModuleCat.of R R) ⟶ ((S).X n).obj) :
    (s.app (op P)).hom (1 : R) = ((generator p k B σ a n).app (op P)).hom
      (((presheaf p k B σ a n).map f.op).hom
        (representative p k B σ a n Q ((s.app (op ((ι).obj Q))).hom (1 : R)))) :=
  SheafificationRestriction.SheafificationRestrictionGenerators.section_generator (generator p k B σ a n)
    (ModuleCat.of R R) s f.op (1 : R) _
    (generator_representative p k B σ a n Q ((s.app (op ((ι).obj Q))).hom (1 : R))).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicGenerators.BigCrystallineIntrinsicGenerators
