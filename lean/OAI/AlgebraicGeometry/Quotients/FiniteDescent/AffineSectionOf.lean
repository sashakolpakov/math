import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperProduct
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine Section Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover

noncomputable section

/-! Finite affine covers given by sections of one line bundle, and their products. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

structure Data (X : Scheme.{u}) where
  lineBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X
  I : Type
  [fintype : Fintype I]
  sectionHom : I → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ lineBundle.sheaf)
  covers : ∀ x : X, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (sectionHom i)
  affine : ∀ i, IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (sectionHom i))

attribute [instance] Data.fintype

def Data.ofAffine (X : Scheme.{u}) [IsAffine X] : Data X where
  lineBundle := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X
  I := Unit
  sectionHom _ := 𝟙 _
  covers x := ⟨(), by
    change x ∈ @AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing X (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (𝟙 _)
    rw [AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso]
    trivial⟩
  affine _ := by
    change IsAffineOpen (@AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing X (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (𝟙 _))
    rw [AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing_of_isIso]
    exact isAffineOpen_top X

def Data.pullback {X Y : Scheme.{u}} (D : Data Y) (f : X ⟶ Y) [IsAffineHom f] : Data X where
  lineBundle := D.lineBundle.pullback f
  I := D.I
  sectionHom i := AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (D.sectionHom i)
  covers x := by
    obtain ⟨i, hi⟩ := D.covers (f x)
    exact ⟨i, (SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f D.lineBundle (D.sectionHom i)).symm ▸ hi⟩
  affine i := by
    change IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f (D.sectionHom i)))
    rw [SectionBase.Construction.SectionBaseChange.nonvanishing_pullback f D.lineBundle (D.sectionHom i)]
    exact (D.affine i).preimage f

theorem affine_pullback_open {S X Y : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (g : Y ⟶ S) {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let p := pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S)
    (Category.comp_id _) (Category.comp_id _)
  have : IsOpenImmersion p := by dsimp only [p]; infer_instance
  have hp : p.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    apply TopologicalSpace.Opens.ext
    simp only [Scheme.Hom.coe_opensRange, p, Scheme.Pullback.range_map, Scheme.Opens.range_ι]
    rfl
  rw [← hp]
  exact isAffineOpen_opensRange p

theorem external_nonvanishing {S X Y : Scheme.{u}}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (f : X ⟶ S) (g : Y ⟶ S)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ M.sheaf) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (BinaryTensorId.Construction.BinaryTensorMap.tensorSection
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst f g) s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.snd f g) t)) =
    pullback.fst f g ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓
      pullback.snd f g ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t :=
  (TensorSection.Construction.TensorSectionLocus.nonvanishing
    (L := L.pullback (pullback.fst f g)) (M := M.pullback (pullback.snd f g))
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst f g) s) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.snd f g) t)).trans
      (congrArg₂ (· ⊓ ·)
        (SectionBase.Construction.SectionBaseChange.nonvanishing_pullback (pullback.fst f g) L s)
        (SectionBase.Construction.SectionBaseChange.nonvanishing_pullback (pullback.snd f g) M t))

def Data.product {S X Y : Scheme.{u}} [IsAffine S]
    (D : Data X) (E : Data Y) (f : X ⟶ S) (g : Y ⟶ S) : Data (Limits.pullback f g) where
  lineBundle := (D.lineBundle.pullback (pullback.fst f g)).tensor
    (E.lineBundle.pullback (pullback.snd f g))
  I := D.I × E.I
  sectionHom i := BinaryTensorId.Construction.BinaryTensorMap.tensorSection
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst f g) (D.sectionHom i.1))
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.snd f g) (E.sectionHom i.2))
  covers x := by
    change ∃ i : D.I × E.I, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
      (BinaryTensorId.Construction.BinaryTensorMap.tensorSection
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst f g) (D.sectionHom i.1))
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.snd f g) (E.sectionHom i.2)))
    obtain ⟨i, hi⟩ := D.covers (pullback.fst f g x)
    obtain ⟨j, hj⟩ := E.covers (pullback.snd f g x)
    refine ⟨(i, j), ?_⟩
    rw [external_nonvanishing D.lineBundle E.lineBundle f g]
    exact ⟨hi, hj⟩
  affine i := by
    change IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing
      (BinaryTensorId.Construction.BinaryTensorMap.tensorSection
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.fst f g) (D.sectionHom i.1))
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (pullback.snd f g) (E.sectionHom i.2))))
    rw [external_nonvanishing D.lineBundle E.lineBundle f g]
    exact affine_pullback_open f g (D.affine i.1) (E.affine i.2)

def finiteProduct {S : Scheme.{u}} [IsAffine S] :
    {n : ℕ} → (P : Fin n → Over S) → (∀ i, Data (P i).left) →
      Data (ProperProduct.Construction.FiniteProperProduct.product P).left
  | 0, _, _ => Data.ofAffine S
  | _ + 1, P, D => (D 0).product
      (finiteProduct (fun i => P i.succ) (fun i => D i.succ))
      (P 0).hom (ProperProduct.Construction.FiniteProperProduct.product (fun i => P i.succ)).hom

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionOf.Construction.AffineSectionCover
