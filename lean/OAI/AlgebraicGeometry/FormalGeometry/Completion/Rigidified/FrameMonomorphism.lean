import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedFrameClassification
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantFamilyFrameRigidity

/-! # Frame Monomorphism -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The normalized-frame scheme of a line bundle on a proper integral
constant family is a monomorphism over its base. Its uniqueness on every
test scheme is derived from the actual global-functions theorem. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {A X S : Scheme.{u}}
  (a : A ⟶ Spec (.of K)) [IsIntegral A] [IsProper a]
  [IsAffine S] {π : X ⟶ S} [IsProper π]
  (q : X ⟶ A) (tS : S ⟶ Spec (.of K)) (hX : IsPullback q π a tS)
  {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X} (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)
  (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
  (r : (Scheme.Modules.pullback s).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S)

include hX

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrame_affinePoints_subsingleton (T : Over S) [IsAffine T.left] :
    Subsingleton (T ⟶ D.rigidifiedFrameScheme s hs r) := by
  let f := pullback.fst π T.hom
  let ρ := pullback.snd π T.hom
  let hp : IsPullback f ρ π T.hom := IsPullback.of_hasPullback π T.hom
  let b := NormalizedFrameClassification.Construction.cartesianSection f ρ π T.hom hp s hs
  let E := D.rigidifiedTrivializationPointEquiv f ρ T.hom hp s hs r
  refine ⟨fun v w => E.symm.injective ?_⟩
  apply Subtype.ext
  exact ConstantFamilyFrameRigidity.Construction.properConstantFamily_normalizedFrame_unique a (f ≫ q) ρ (T.hom ≫ tS)
    (hp.paste_horiz hX) f b (NormalizedFrameClassification.Construction.cartesianSection_snd f ρ π T.hom hp s hs)
    T.hom s (NormalizedFrameClassification.Construction.cartesianSection_fst f ρ π T.hom hp s hs) L.sheaf r
    (E.symm v).val (E.symm w).val (E.symm v).property (E.symm w).property

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.rigidifiedFrame_mono : Mono (D.rigidifiedFrameScheme s hs r).hom := by
  constructor
  intro Z v w hvw
  apply Z.affineCover.hom_ext v w
  intro i
  let g := (Z.affineCover.f i ≫ v) ≫ (D.rigidifiedFrameScheme s hs r).hom
  let v' : Over.mk g ⟶ D.rigidifiedFrameScheme s hs r := Over.homMk (Z.affineCover.f i ≫ v) rfl
  let w' : Over.mk g ⟶ D.rigidifiedFrameScheme s hs r := Over.homMk (Z.affineCover.f i ≫ w) (by
    dsimp [g]
    simpa only [Category.assoc] using congrArg (fun z => Z.affineCover.f i ≫ z) hvw.symm)
  have : IsAffine (Over.mk g).left := inferInstanceAs (IsAffine (Z.affineCover.X i))
  have := D.rigidifiedFrame_affinePoints_subsingleton a q tS hX s hs r (Over.mk g)
  exact congrArg Over.Hom.left (Subsingleton.elim v' w')

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
