import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange

/-! # Kernel Character Squares -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelCharacterSquares

noncomputable section

/-! Kernel characters and their actual descended line bundles are
functorial under commuting squares of group covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {A B A' B' : Over S}
  [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
  (s : B' ⟶ B) (t : A' ⟶ A) [IsMonHom s] [IsMonHom t]
  (w : t ≫ f = f' ≫ s)

def kernelSquareMap : Picard.Homomorphisms.Kernel.Construction.kernelScheme f' ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f :=
  Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift f (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f' ≫ t) (by
    rw [Category.assoc, w, ← Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.one_comp])

omit [GrpObj A] [GrpObj A'] [IsMonHom f] [IsMonHom f'] [IsMonHom t] in
theorem kernelSquareMap_inclusion :
    kernelSquareMap f f' s t w ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f = Picard.Homomorphisms.Kernel.Construction.kernelInclusion f' ≫ t :=
  Picard.Homomorphisms.FrobeniusKernelBaseChange.Construction.kernelLift_inclusion _ _ _

instance kernelSquareMap_isMonHom : IsMonHom (kernelSquareMap f f' s t w) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  have : IsMonHom (kernelSquareMap f f' s t w ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := by
    rw [kernelSquareMap_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)

theorem kernelSquareMap_difference {T : Over S} (x y : T ⟶ A')
    (h : x ≫ f' = y ≫ f') :
    CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f' x y h ≫ kernelSquareMap f f' s t w =
      CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f (x ≫ t) (y ≫ t)
        (by rw [Category.assoc, w, ← Category.assoc, h, Category.assoc, ← w, ← Category.assoc]) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [Category.assoc, kernelSquareMap_inclusion, ← Category.assoc,
    CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, MonObj.mul_comp, GrpObj.inv_comp]

variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
  (hχ : ∀ {T U : Over S} (a : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
    Units.map a.left.appTop.hom (χ T x) = χ U (a ≫ x))

def squareKernelCharacter (T : Over S) : (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') →* Γ(T.left, ⊤)ˣ :=
  (χ T).comp (IsMonHom.monoidHom (kernelSquareMap f f' s t w) T)

include hχ in
theorem squareKernelCharacter_natural {T U : Over S} (a : U ⟶ T)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    Units.map a.left.appTop.hom (squareKernelCharacter f f' s t w χ T x) =
      squareKernelCharacter f f' s t w χ U (a ≫ x) :=
  (hχ a (x ≫ kernelSquareMap f f' s t w)).trans
    (congrArg (χ U) (Category.assoc a x (kernelSquareMap f f' s t w)).symm)

include hχ in
theorem differenceScalar_square {T : Scheme.{u}}
    (z : T ⟶ B'.left) (x y : T ⟶ A'.left)
    (hx : x ≫ f'.left = z) (hy : y ≫ f'.left = z) :
    CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f' (squareKernelCharacter f f' s t w χ) z x y hx hy =
      CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ (z ≫ s.left) (x ≫ t.left) (y ≫ t.left)
        (by rw [Category.assoc, ← Over.comp_left, w, Over.comp_left, ← Category.assoc, hx])
        (by rw [Category.assoc, ← Over.comp_left, w, Over.comp_left, ← Category.assoc, hy]) := by
  let U := Over.mk (z ≫ B'.hom)
  let px : U ⟶ A' := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint f' z x hx
  let py : U ⟶ A' := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint f' z y hy
  have hd : px ≫ f' = py ≫ f' :=
    (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f' z x hx).trans (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f' z y hy).symm
  have hpx : px.left ≫ f'.left = z := hx
  have hpy : py.left ≫ f'.left = z := hy
  have hnew := CartierDuality.CharacterTranslations.Construction.KernelCharacters.differenceScalar_over f' (squareKernelCharacter f f' s t w χ)
    (squareKernelCharacter_natural f f' s t w χ hχ) (T := U) z px py hpx hpy
  have htx : (px ≫ t).left ≫ f.left = z ≫ s.left := by
    change (x ≫ t.left) ≫ f.left = _
    rw [Category.assoc, ← Over.comp_left, w, Over.comp_left, ← Category.assoc, hx]
  have hty : (py ≫ t).left ≫ f.left = z ≫ s.left := by
    change (y ≫ t.left) ≫ f.left = _
    rw [Category.assoc, ← Over.comp_left, w, Over.comp_left, ← Category.assoc, hy]
  have hold := CartierDuality.CharacterTranslations.Construction.KernelCharacters.differenceScalar_over f χ hχ (T := U) (z ≫ s.left) (px ≫ t) (py ≫ t) htx hty
  exact hnew.trans ((congrArg (fun a => (χ U a).val)
    (kernelSquareMap_difference f f' s t w px py hd)).trans hold.symm)

def characterLineDatum_squareIso :
    (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f.left f'.left s.left t.left (congrArg Over.Hom.left w)).obj
      (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)) ≅
      CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData
        (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f' (squareKernelCharacter f f' s t w χ)
          (squareKernelCharacter_natural f f' s t w χ hχ)) := by
  apply CartierDuality.ScalarDescentSymmetry.Construction.LineDescent.nativeDatumIso_of_framedScalars _ _ _
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)) t.left)
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A'.left))
  intro T z x y hx hy
  have hs := CartierDuality.FramedBaseChange.Construction.LineDescent.framedDescentScalar_square f.left f'.left s.left t.left
    (congrArg Over.Hom.left w) (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ))
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)) z x y hx hy
  have hold := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar f χ hχ (z ≫ s.left) (x ≫ t.left) (y ≫ t.left)
    (by rw [Category.assoc, ← Over.comp_left, w, Over.comp_left, ← Category.assoc, hx])
    (by rw [Category.assoc, ← Over.comp_left, w, Over.comp_left, ← Category.assoc, hy])
  have hnew := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar f' (squareKernelCharacter f f' s t w χ)
    (squareKernelCharacter_natural f f' s t w χ hχ) z x y hx hy
  exact hs.trans (hold.trans ((differenceScalar_square f f' s t w χ hχ z x y hx hy).symm.trans hnew.symm))

variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left]

theorem characterDescendedLine_square :
    Nonempty ((Scheme.Modules.pullback s.left).obj (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ).sheaf ≅
      (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f' (squareKernelCharacter f f' s t w χ)
        (squareKernelCharacter_natural f f' s t w χ hχ)).sheaf) :=
  CartierDuality.CharacterLineBaseChange.Construction.LineDescent.recoveredLine_square_iso f.left f'.left s.left t.left (congrArg Over.Hom.left w)
    (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ)
    (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f' (squareKernelCharacter f f' s t w χ)
      (squareKernelCharacter_natural f f' s t w χ hχ))
    (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ))
    (CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f' (squareKernelCharacter f f' s t w χ)
      (squareKernelCharacter_natural f f' s t w χ hχ)))
    (CartierDuality.OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso f.left (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A.left).locallyTrivial)
    (CartierDuality.OrdinaryGlobalLineDescent.Construction.LineDescent.nativeDescendedLineRecoveryIso f'.left
      (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f' (squareKernelCharacter f f' s t w χ)
        (squareKernelCharacter_natural f f' s t w χ hχ)) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial A'.left).locallyTrivial)
    (characterLineDatum_squareIso f f' s t w χ hχ)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelCharacterSquares
