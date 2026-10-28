import OAI.AlgebraicGeometry.SheafCohomology.Sheaves
import OAI.AlgebraicGeometry.SheafCohomology.SheafRestriction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-! # Tensor Bundles -/

namespace OAI.AlgebraicGeometry.SheafCohomology.TensorBundles.Projective

noncomputable section

/-! Local trivializations of the actual sheafified tensor products. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def localTensor (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens)
    (M N : SheafOfModules (A.carrier.ringCatSheaf.over U)) :
    SheafOfModules (A.carrier.ringCatSheaf.over U) :=
  (PresheafOfModules.sheafification (𝟙 (A.carrier.ringCatSheaf.over U).obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (Over.forget U).op ⋙ A.carrier.presheaf) M.val N.val)

def localTensorIso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens)
    {M M' N N' : SheafOfModules (A.carrier.ringCatSheaf.over U)}
    (e : M ≅ M') (f : N ≅ N') : localTensor A U M N ≅ localTensor A U M' N' :=
  (PresheafOfModules.sheafification (𝟙 (A.carrier.ringCatSheaf.over U).obj)).mapIso
    (MonoidalCategory.tensorIso
      (C := PresheafOfModules
        (((Over.forget U).op ⋙ A.carrier.presheaf) ⋙ forget₂ CommRingCat RingCat))
      ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f))

def tensorOverIso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens)
    (M N : A.carrier.Modules) :
    localTensor A U (M.over U) (N.over U) ≅ (Sheaves.Projective.sheafTensor A M N).over U :=
  (PresheafOfModules.sheafification (𝟙 (A.carrier.ringCatSheaf.over U).obj)).mapIso
    (Functor.Monoidal.μIso
      (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) A.carrier.presheaf)
      M.val N.val) ≪≫
    SheafRestriction.Projective.overSheafificationIso A.carrier.ringCatSheaf U
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := A.carrier.presheaf) M.val N.val)

def localTensorUnitIso (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens) :
    localTensor A U (SheafOfModules.unit _) (SheafOfModules.unit _) ≅
      SheafOfModules.unit (A.carrier.ringCatSheaf.over U) :=
  (PresheafOfModules.sheafification (𝟙 (A.carrier.ringCatSheaf.over U).obj)).mapIso
    (MonoidalCategory.leftUnitor
      (C := PresheafOfModules
        (((Over.forget U).op ⋙ A.carrier.presheaf) ⋙ forget₂ CommRingCat RingCat))
      (SheafOfModules.unit (A.carrier.ringCatSheaf.over U)).val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (A.carrier.ringCatSheaf.over U).obj)).counit).app (SheafOfModules.unit _)

/-- A genuine open-scheme trivialization gives one on the equivalent slice site. -/
def overFrame (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens) (M : A.carrier.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U) :=
  (Functor.FullyFaithful.ofFullyFaithful (Scheme.Modules.overEquiv U).functor).preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit A.carrier.ringCatSheaf).symm)

/-- Transport a slice-site trivialization back to the actual open subscheme. -/
def frameFromOver (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens) (M : A.carrier.Modules)
    (e : M.over U ≅ SheafOfModules.unit (A.carrier.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
      U.sheafOfModulesEquivOverUnit A.carrier.ringCatSheaf

/-- Tensoring two local rank-one trivializations gives an actual sheaf frame. -/
def sheafTensorFrame (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (U : A.carrier.Opens)
    (M N : A.carrier.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (f : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (Sheaves.Projective.sheafTensor A M N).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  frameFromOver A U (Sheaves.Projective.sheafTensor A M N)
    ((tensorOverIso A U M N).symm ≪≫
      localTensorIso A U (overFrame A U M e) (overFrame A U N f) ≪≫
        localTensorUnitIso A U)

/-- Every actual tensor power is trivial on any open trivializing the original bundle. -/
def tensorPowerFrame (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A)
    (U : A.carrier.Opens)
    (e : L.sheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ∀ n, (Sheaves.Projective.tensorPower A L n).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => sheafTensorFrame A U (Sheaves.Projective.tensorPower A L n) L.sheaf
      (tensorPowerFrame A L U e n) e

/-- The ProjectiveCohomology tensor power, now equipped with proved rank-one local triviality. -/
def tensorPowerLineBundle (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) (n : ℕ) :
    Sheaves.Projective.LineBundle A where
  sheaf := Sheaves.Projective.tensorPower A L n
  locallyTrivial x := ⟨L.trivializingOpen x, L.mem_trivializingOpen x,
    ⟨Projective.tensorPowerFrame A L (L.trivializingOpen x) (L.trivialization x) n⟩⟩

@[simp] theorem tensorPowerLineBundle_sheaf (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : Sheaves.Projective.LineBundle A) (n : ℕ) :
    (tensorPowerLineBundle A L n).sheaf = Sheaves.Projective.tensorPower A L n := rfl

/-- Tensoring two actual line-bundle sheaves again gives an actual line bundle. -/
def tensorLineBundle (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L M : Sheaves.Projective.LineBundle A) : Sheaves.Projective.LineBundle A where
  sheaf := Sheaves.Projective.sheafTensor A L.sheaf M.sheaf
  locallyTrivial x :=
    ⟨L.trivializingOpen x ⊓ M.trivializingOpen x,
      ⟨L.mem_trivializingOpen x, M.mem_trivializingOpen x⟩,
      ⟨sheafTensorFrame A _ L.sheaf M.sheaf
        (L.trivializationOn x _ inf_le_left) (M.trivializationOn x _ inf_le_right)⟩⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.TensorBundles.Projective
