import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTranslations
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterBaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Kernel Character Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange

noncomputable section

/-!
# CartierDuality: arbitrary base change of actual unit-valued kernel characters
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelBaseChange.Construction
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.KernelCharacters

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
    {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The canonical scheme-theoretic kernel comparison preserves the actual group law. -/
theorem kernelBaseChangeIso_isMonHom : IsMonHom (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).hom := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f)) :=
    inferInstanceAs (Mono (equalizer.ι ((Over.pullback s).map f) 1))
  have : IsMonHom ((Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).hom ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f)) := by
    rw [Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f))

theorem kernelBaseChangeIso_inv_isMonHom : IsMonHom (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv := by
  have := kernelBaseChangeIso_isMonHom s f
  infer_instance

/-- A kernel point after base change gives its original kernel point through the pullback adjunction. -/
def baseChangeKernelPoint (T : Over S') :
    (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) →* ((Over.map s).obj T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) := by
  have := kernelBaseChangeIso_inv_isMonHom s f
  exact (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) T).symm.toMonoidHom.comp
    (IsMonHom.monoidHom (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv T)

/-- The original point comparison is natural in every test-scheme map. -/
theorem pullbackPoint_symm_precomp (G : Grp (Over S)) {T U : Over S'}
    (t : U ⟶ T) (x : T ⟶ (Over.pullback s).obj G.X) :
    (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G U).symm (t ≫ x) =
      (Over.map s).map t ≫ (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s G T).symm x :=
  (Over.mapPullbackAdj s).homEquiv_naturality_left_symm t x

theorem baseChangeKernelPoint_natural {T U : Over S'} (t : U ⟶ T)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    baseChangeKernelPoint s f U (t ≫ x) = (Over.map s).map t ≫ baseChangeKernelPoint s f T x := by
  change (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) U).symm
    ((t ≫ x) ≫ (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv) = _
  rw [Category.assoc]
  exact pullbackPoint_symm_precomp s (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) t (x ≫ (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv)

omit [IsMonHom f] in
/-- The original-point comparison commutes with the actual morphism of groups. -/
theorem pullbackPoint_symm_comp (T : Over S') (x : T ⟶ (Over.pullback s).obj A) :
    (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk B) T).symm (x ≫ (Over.pullback s).map f) =
      (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm x ≫ f :=
  (Over.mapPullbackAdj s).homEquiv_naturality_right_symm x f

/-- The canonical kernel-point comparison retains the actual inclusion in the original group. -/
theorem baseChangeKernelPoint_inclusion (T : Over S')
    (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    baseChangeKernelPoint s f T z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f =
      (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm
        (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f)) := by
  have hi : (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv ≫ (Over.pullback s).map (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) =
      Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f) := by
    rw [← Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso_inclusion s f, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h := (Over.mapPullbackAdj s).homEquiv_naturality_right_symm
    (z ≫ (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).inv) (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)
  exact h.symm.trans (congrArg (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm
    (by rw [Category.assoc, hi]))

omit [IsMonHom f] in
/-- Equal images after base change have equal images in the original group. -/
theorem originalPoints_equalImage (T : Over S') (x y : T ⟶ (Over.pullback s).obj A)
    (h : x ≫ (Over.pullback s).map f = y ≫ (Over.pullback s).map f) :
    (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm x ≫ f =
      (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm y ≫ f :=
  (pullbackPoint_symm_comp s f T x).symm.trans
    ((congrArg (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk B) T).symm h).trans
      (pullbackPoint_symm_comp s f T y))

/-- Arbitrary base change preserves the exact kernel difference, including infinitesimal points. -/
theorem baseChangeKernelPoint_difference (T : Over S') (x y : T ⟶ (Over.pullback s).obj A)
    (h : x ≫ (Over.pullback s).map f = y ≫ (Over.pullback s).map f) :
    baseChangeKernelPoint s f T (KernelCharacterGluing.Construction.KernelCharacters.kernelDifference ((Over.pullback s).map f) x y h) =
      KernelCharacterGluing.Construction.KernelCharacters.kernelDifference f ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm x)
        ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm y) (originalPoints_equalImage s f T x y h) := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [baseChangeKernelPoint_inclusion, KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion, KernelCharacterGluing.Construction.KernelCharacters.kernelDifference_inclusion,
    map_mul, map_inv]

variable (χ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))

/-- Restriction of the actual character through the canonical native kernel base change. -/
def baseChangedKernelCharacter (T : Over S') :
    (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) →* Γ(T.left, ⊤)ˣ :=
  (χ ((Over.map s).obj T)).comp (baseChangeKernelPoint s f T)

omit [GrpObj A] [GrpObj B] [IsMonHom f] in
/-- The native covering morphism commutes with its two base-change projections. -/
theorem pullbackCover_square :
    pullback.fst A.hom s ≫ f.left = ((Over.pullback s).map f).left ≫ pullback.fst B.hom s :=
  (pullback.lift_fst _ _ _).symm

include hχ in
theorem baseChangedKernelCharacter_natural {T U : Over S'} (t : U ⟶ T)
    (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f)) :
    Units.map t.left.appTop.hom (baseChangedKernelCharacter s f χ T x) =
      baseChangedKernelCharacter s f χ U (t ≫ x) :=
  (hχ ((Over.map s).map t) (baseChangeKernelPoint s f T x)).trans
    (congrArg (χ ((Over.map s).obj U)) (baseChangeKernelPoint_natural s f t x).symm)

include hχ in
/-- The difference scalar after base change is the original scalar on the projected test pair. -/
theorem differenceScalar_baseChange {T : Scheme.{u}}
    (q : T ⟶ ((Over.pullback s).obj B).left) (x y : T ⟶ ((Over.pullback s).obj A).left)
    (hx : x ≫ ((Over.pullback s).map f).left = q) (hy : y ≫ ((Over.pullback s).map f).left = q) :
    KernelCharacterGluing.Construction.KernelCharacters.differenceScalar ((Over.pullback s).map f) (baseChangedKernelCharacter s f χ) q x y hx hy =
      KernelCharacterGluing.Construction.KernelCharacters.differenceScalar f χ (q ≫ pullback.fst B.hom s) (x ≫ pullback.fst A.hom s)
        (y ≫ pullback.fst A.hom s)
        (by rw [Category.assoc, pullbackCover_square, ← Category.assoc, hx])
        (by rw [Category.assoc, pullbackCover_square, ← Category.assoc, hy]) := by
  let U := Over.mk (q ≫ ((Over.pullback s).obj B).hom)
  let px : U ⟶ (Over.pullback s).obj A := KernelCharacterGluing.Construction.KernelCharacters.coverPoint ((Over.pullback s).map f) q x hx
  let py : U ⟶ (Over.pullback s).obj A := KernelCharacterGluing.Construction.KernelCharacters.coverPoint ((Over.pullback s).map f) q y hy
  have hd : px ≫ (Over.pullback s).map f = py ≫ (Over.pullback s).map f :=
    (KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp ((Over.pullback s).map f) q x hx).trans
      (KernelCharacterGluing.Construction.KernelCharacters.coverPoint_comp ((Over.pullback s).map f) q y hy).symm
  have hpx : px.left ≫ ((Over.pullback s).map f).left = q := hx
  have hpy : py.left ≫ ((Over.pullback s).map f).left = q := hy
  have hnew := CharacterTranslations.Construction.KernelCharacters.differenceScalar_over ((Over.pullback s).map f) (baseChangedKernelCharacter s f χ)
    (baseChangedKernelCharacter_natural s f χ hχ) (T := U) q px py hpx hpy
  let ax := (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) U).symm px
  let ay := (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) U).symm py
  have hax : ax.left ≫ f.left = q ≫ pullback.fst B.hom s := by
    change (x ≫ pullback.fst A.hom s) ≫ f.left = _
    rw [Category.assoc, pullbackCover_square, ← Category.assoc, hx]
  have hay : ay.left ≫ f.left = q ≫ pullback.fst B.hom s := by
    change (y ≫ pullback.fst A.hom s) ≫ f.left = _
    rw [Category.assoc, pullbackCover_square, ← Category.assoc, hy]
  have hold := CharacterTranslations.Construction.KernelCharacters.differenceScalar_over f χ hχ (T := (Over.map s).obj U)
    (q ≫ pullback.fst B.hom s) ax ay hax hay
  exact hnew.trans ((congrArg (fun z => (χ ((Over.map s).obj U) z).val)
    (baseChangeKernelPoint_difference s f U px py hd)).trans hold.symm)

/-- The base-changed character constructs full native ordinary line gluing. -/
def baseChangedCharacterLineDatum : Picard.Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent ((Over.pullback s).map f).left :=
  KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback s).map f) (baseChangedKernelCharacter s f χ)
    (baseChangedKernelCharacter_natural s f χ hχ)

/-- The whole ordinary datum of the base-changed character is the pullback of the original datum. -/
def characterLineDatum_baseChangeIso :
    (Picard.Homomorphisms.ModuleHomBaseChange.Construction.descentSquareFunctor f.left ((Over.pullback s).map f).left
      (pullback.fst B.hom s) (pullback.fst A.hom s) (pullbackCover_square s f)).obj
        (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ)) ≅
      AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (baseChangedCharacterLineDatum s f χ hχ) := by
  apply ScalarDescentSymmetry.Construction.LineDescent.nativeDatumIso_of_framedScalars _ _ _
    (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)) (pullback.fst A.hom s))
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback s).obj A).left))
  intro T q x y hx hy
  have hs := FramedBaseChange.Construction.LineDescent.framedDescentScalar_square f.left ((Over.pullback s).map f).left
    (pullback.fst B.hom s) (pullback.fst A.hom s) (pullbackCover_square s f)
    (AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData (KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum f χ hχ))
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left)) q x y hx hy
  have hold := KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar f χ hχ (q ≫ pullback.fst B.hom s)
    (x ≫ pullback.fst A.hom s) (y ≫ pullback.fst A.hom s)
    (by rw [Category.assoc, pullbackCover_square, ← Category.assoc, hx])
    (by rw [Category.assoc, pullbackCover_square, ← Category.assoc, hy])
  have hnew := KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar ((Over.pullback s).map f) (baseChangedKernelCharacter s f χ)
    (baseChangedKernelCharacter_natural s f χ hχ) q x y hx hy
  exact hs.trans (hold.trans ((differenceScalar_baseChange s f χ hχ q x y hx hy).symm.trans hnew.symm))

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange
