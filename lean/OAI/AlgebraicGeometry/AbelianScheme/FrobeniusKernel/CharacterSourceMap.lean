import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Character Source Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterSourceMap.Construction

noncomputable section

section

/-! A square of original group homomorphisms transports the actual
scheme kernel and its character differences on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations.Construction.KernelCharacters

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)

def kernelSourceSquareMap : Picard.Homomorphisms.Kernel.Construction.kernelScheme f' ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f :=
  equalizer.lift (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f' ≫ a) (by
    rw [Category.assoc, h, ← Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp,
      MonObj.one_comp, MonObj.comp_one])

omit [GrpObj A] [GrpObj A'] [IsMonHom f] [IsMonHom f'] [IsMonHom a] in
theorem kernelSourceSquareMap_inclusion :
    kernelSourceSquareMap f f' a b h ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f = Picard.Homomorphisms.Kernel.Construction.kernelInclusion f' ≫ a :=
  equalizer.lift_ι _ _

instance kernelSourceSquareMap_isMonHom : IsMonHom (kernelSourceSquareMap f f' a b h) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f (1 : A ⟶ B)))
  have : IsMonHom (kernelSourceSquareMap f f' a b h ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := by
    rw [kernelSourceSquareMap_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp (kernelSourceSquareMap f f' a b h) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)

include h in
omit [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    [IsMonHom f] [IsMonHom f'] [IsMonHom a] [IsMonHom b] in
theorem sourceSquare_equalImages {T : Over S} (x y : T ⟶ A') (he : x ≫ f' = y ≫ f') :
    (x ≫ a) ≫ f = (y ≫ a) ≫ f := by
  rw [Category.assoc, Category.assoc, h, ← Category.assoc, ← Category.assoc, he]

theorem kernelSourceSquareMap_difference {T : Over S} (x y : T ⟶ A') (he : x ≫ f' = y ≫ f') :
    CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f' x y he ≫ kernelSourceSquareMap f f' a b h =
      CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f (x ≫ a) (y ≫ a) (sourceSquare_equalImages f f' a b h x y he) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f (1 : A ⟶ B)))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [Category.assoc, kernelSourceSquareMap_inclusion, ← Category.assoc,
    CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, MonObj.mul_comp]
  exact congrArg (fun z => z * (y ≫ a)) (map_inv (IsMonHom.monoidHom a T) x)

variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
variable (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
  Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

def kernelCharacterSourceRestriction (T : Over S) : (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') →* Γ(T.left, ⊤)ˣ :=
  (χ T).comp (IsMonHom.monoidHom (kernelSourceSquareMap f f' a b h) T)

include hχ in
theorem kernelCharacterSourceRestriction_natural {T U : Over S} (t : U ⟶ T)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    Units.map t.left.appTop.hom (kernelCharacterSourceRestriction f f' a b h χ T x) =
      kernelCharacterSourceRestriction f f' a b h χ U (t ≫ x) :=
  (hχ t (x ≫ kernelSourceSquareMap f f' a b h)).trans
    (congrArg (χ U) (Category.assoc t x (kernelSourceSquareMap f f' a b h)).symm)

end

/-! Original source squares preserve the full regular scalar cocycle
used to descend a kernel-character line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations.Construction.KernelCharacters

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)
variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
variable (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
  Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

include hχ in
theorem differenceScalar_sourceSquare {T : Scheme}
    (q : T ⟶ B'.left) (x y : T ⟶ A'.left)
    (hx : x ≫ f'.left = q) (hy : y ≫ f'.left = q) :
    CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f' (kernelCharacterSourceRestriction f f' a b h χ) q x y hx hy =
      CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ (q ≫ b.left) (x ≫ a.left) (y ≫ a.left)
        (by rw [Category.assoc, ← Over.comp_left, h, Over.comp_left, ← Category.assoc, hx])
        (by rw [Category.assoc, ← Over.comp_left, h, Over.comp_left, ← Category.assoc, hy]) := by
  let U := Over.mk (q ≫ B'.hom)
  let px : U ⟶ A' := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint f' q x hx
  let py : U ⟶ A' := CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint f' q y hy
  have hd : px ≫ f' = py ≫ f' := (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f' q x hx).trans (CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp f' q y hy).symm
  have hpx : px.left ≫ f'.left = q := hx
  have hpy : py.left ≫ f'.left = q := hy
  have hnew := CartierDuality.CharacterTranslations.Construction.KernelCharacters.differenceScalar_over f' (kernelCharacterSourceRestriction f f' a b h χ)
    (kernelCharacterSourceRestriction_natural f f' a b h χ hχ) (T := U) q px py hpx hpy
  have hax : (px ≫ a).left ≫ f.left = q ≫ b.left := by
    change (x ≫ a.left) ≫ f.left = _
    rw [Category.assoc, ← Over.comp_left, h, Over.comp_left, ← Category.assoc, hx]
  have hay : (py ≫ a).left ≫ f.left = q ≫ b.left := by
    change (y ≫ a.left) ≫ f.left = _
    rw [Category.assoc, ← Over.comp_left, h, Over.comp_left, ← Category.assoc, hy]
  have hold := CartierDuality.CharacterTranslations.Construction.KernelCharacters.differenceScalar_over f χ hχ (T := U) (q ≫ b.left) (px ≫ a) (py ≫ a) hax hay
  exact hnew.trans ((congrArg (fun z => (χ U z).val)
    (kernelSourceSquareMap_difference f f' a b h px py hd)).trans hold.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterSourceMap.Construction
