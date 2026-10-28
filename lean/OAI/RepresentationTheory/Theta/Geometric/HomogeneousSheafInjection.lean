import OAI.RepresentationTheory.Theta.Geometric.ParameterizedHomogeneousPicard

/-! # Homogeneous Sheaf Injection -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection

noncomputable section

/-! Sheafification preserves the actual inclusion of homogeneous
Picard classes into the relative Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem homogeneousPicardSheafInclusion_mono : Mono A.homogeneousPicardSheafInclusion := by
  have (T : (Over S)ᵒᵖ) : Mono (A.homogeneousPicardInclusion.app T) :=
    (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective
  have : Mono A.homogeneousPicardInclusion := NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    A.homogeneousPicardInclusion)
  infer_instance

theorem homogeneousPicardSheafInclusion_injective (T : Over S) :
    Function.Injective (A.homogeneousPicardSheafInclusion.hom.app (.op T)) := by
  let := homogeneousPicardSheafInclusion_mono A
  have : Mono A.homogeneousPicardSheafInclusion.hom :=
    inferInstanceAs (Mono ((sheafToPresheaf _ _).map A.homogeneousPicardSheafInclusion))
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

theorem homogeneousSheafClass_forget (T : Over S) (q : A.homogeneousPicardPresheaf.obj (.op T)) :
    A.homogeneousPicardSheafInclusion.hom.app (.op T)
      ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T) q) =
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) q.val :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S) A.homogeneousPicardInclusion) (.op T)) q).symm

end

end OAI.RepresentationTheory.Theta.Geometric.HomogeneousSheafInjection
