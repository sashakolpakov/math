import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeScalar
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection

/-! # Relative Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeCharacters.Construction

noncomputable section

/-! Recover pullback-trivial line bundles from their actual kernel
characters over bases where group-coordinate functions are constant. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelCharacterDetection.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineProducts.Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable {f : A ⟶ B} [IsMonHom f]
variable [IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) A).left.appTop]

def kernelScalarUnitCharacter (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f) (T : Over S) :
    (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ where
  toFun z := Units.map z.left.appTop.hom D.kernelScalar_isUnit.unit
  map_one' := Units.ext (by
    change (1 : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left.appTop D.kernelScalar_isUnit.unit.val = 1
    rw [IsUnit.unit_spec]
    exact RelativeScalar.Construction.kernelCocycle_scalar_one_of_functions D T)
  map_mul' z w := Units.ext (by
    change (z * w).left.appTop D.kernelScalar_isUnit.unit.val =
      z.left.appTop D.kernelScalar_isUnit.unit.val * w.left.appTop D.kernelScalar_isUnit.unit.val
    rw [IsUnit.unit_spec]
    exact RelativeScalar.Construction.kernelCocycle_scalar_mul_of_functions D z w)

theorem kernelScalarUnitCharacter_val (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f) (T : Over S)
    (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    (kernelScalarUnitCharacter D T z).val = z.left.appTop D.kernelScalar := by
  change z.left.appTop D.kernelScalar_isUnit.unit.val = _
  rw [IsUnit.unit_spec]

theorem kernelScalarUnitCharacter_natural (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f)
    {T U : Over S} (t : U ⟶ T) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    Units.map t.left.appTop.hom (kernelScalarUnitCharacter D T z) =
      kernelScalarUnitCharacter D U (t ≫ z) := by
  apply Units.ext
  change t.left.appTop (kernelScalarUnitCharacter D T z).val = _
  rw [kernelScalarUnitCharacter_val, kernelScalarUnitCharacter_val]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop t.left z.left) D.kernelScalar).symm

variable (D E : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent f.left)
variable (e : D.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) (d : E.module ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)

theorem kernelScalar_eq_implies_descentScalar_eq_of_functions
    (h : (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f D e).kernelScalar =
      (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f E d).kernelScalar)
    {T : Over S} (x y : T ⟶ A) (hxy : x ≫ f = y ≫ f) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) =
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar E d (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) := by
  obtain ⟨z, hz⟩ := Picard.Homomorphisms.KernelCharacterDetection.Construction.kernel_action_covers_relation f x y hxy
  have hd := RelativeScalar.Construction.kernelCocycle_value_eq_scalar_of_functions (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f D e) x z
  have he := RelativeScalar.Construction.kernelCocycle_value_eq_scalar_of_functions (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f E d) x z
  have hc : Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalar f D e x z = Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalar f E d x z :=
    hd.trans ((congrArg z.left.appTop h).trans he.symm)
  have hD : Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalar f D e x z =
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) :=
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr D e _ _ _ _ _ _ _ _ _ _ rfl rfl (congrArg Over.Hom.left hz)
  have hE : Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalar f E d x z =
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar E d (x ≫ f).left x.left y.left rfl
        (congrArg Over.Hom.left hxy.symm) :=
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr E d _ _ _ _ _ _ _ _ _ _ rfl rfl (congrArg Over.Hom.left hz)
  exact hD.symm.trans (hc.trans hE)

theorem kernelScalar_eq_implies_fullScalar_eq_of_functions
    (h : (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f D e).kernelScalar =
      (Picard.Homomorphisms.LineKernelCocycle.Construction.framedKernelScalarCocycle f E d).kernelScalar)
    {T : Scheme.{u}} (q : T ⟶ B.left) (x y : T ⟶ A.left)
    (hx : x ≫ f.left = q) (hy : y ≫ f.left = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar D e q x y hx hy = Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar E d q x y hx hy := by
  let T' : Over S := Over.mk (x ≫ A.hom)
  let x' : T' ⟶ A := Over.homMk x rfl
  let y' : T' ⟶ A := Over.homMk y (by
    change y ≫ A.hom = x ≫ A.hom
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, hx, hy])
  have hxy : x' ≫ f = y' ≫ f := Over.OverMorphism.ext (hx.trans hy.symm)
  have hs := kernelScalar_eq_implies_descentScalar_eq_of_functions D E e d h x' y' hxy
  have hD := Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr D e (x' ≫ f).left q x'.left x y'.left y
    rfl (congrArg Over.Hom.left hxy.symm) hx hy hx rfl rfl
  have hE := Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr E d (x' ≫ f).left q x'.left x y'.left y
    rfl (congrArg Over.Hom.left hxy.symm) hx hy hx rfl rfl
  exact hD.symm.trans (hs.trans hE)

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

theorem lineIso_of_kernelScalar_eq_of_functions (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (eL : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (eM : (Scheme.Modules.pullback f.left).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)
    (h : (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L eL).kernelScalar =
      (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f M eM).kernelScalar) : Nonempty (L.sheaf ≅ M.sheaf) :=
  CartierDuality.CharacterLineProducts.Construction.LineDescent.lineIso_of_framedScalars f.left L M eL eM
    (kernelScalar_eq_implies_fullScalar_eq_of_functions (f := f)
      (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left L.sheaf) (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f.left M.sheaf) eL eM h)

theorem pullbackTrivialLine_from_kernelCharacter (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
    (eL : (Scheme.Modules.pullback f.left).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left) :
    ∃ (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
      (hχ : ∀ {T U : Over S} (t : U ⟶ T) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
        Units.map t.left.appTop.hom (χ T z) = χ U (t ≫ z)),
      Nonempty (L.sheaf ≅ (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf) := by
  let C := Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f L eL
  let χ := kernelScalarUnitCharacter C
  have hχ : ∀ {T U : Over S} (t : U ⟶ T) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T z) = χ U (t ≫ z) :=
    fun t z => kernelScalarUnitCharacter_natural C t z
  refine ⟨χ, hχ, lineIso_of_kernelScalar_eq_of_functions L _ eL
    (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLineFrame f χ hχ) ?_⟩
  have hc := CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine_kernelScalar f χ hχ
  have hv : (χ (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) (𝟙 _)).val = C.kernelScalar := by
    rw [kernelScalarUnitCharacter_val, Over.id_left, Scheme.Hom.id_appTop]
    rfl
  exact (hc.trans hv).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeCharacters.Construction
