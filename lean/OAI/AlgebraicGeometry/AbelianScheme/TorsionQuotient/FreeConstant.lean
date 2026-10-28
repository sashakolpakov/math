import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.ConstantPointsIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection
import Mathlib.CategoryTheory.EquivalenceRelation
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Free Constant -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FreeConstant.FreeConstantAction

/-! The scheme relation of a free finite constant-group action. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme

universe u

variable {S : Scheme.{u}} (X : Over S) (G : Type u) [Group G]

structure Data where
  map : G → (X ⟶ X)
  map_one : map 1 = 𝟙 X
  map_mul : ∀ g h, map g ≫ map h = map (g * h)
  free : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Over.mk s ⟶ X) (g h : G), a ≫ map g = a ≫ map h → g = h

variable {X G} (d : Data X G)

noncomputable abbrev relation : Over S :=
  Over.mk ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom ≫ X.hom)

noncomputable def source : relation (X := X) (G := G) ⟶ X :=
  Over.homMk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom rfl

noncomputable def inclusion (g : G) : X ⟶ relation (X := X) (G := G) :=
  Over.homMk (Sigma.ι (fun _ : G => X.left) g) (by
    change Sigma.ι (fun _ : G => X.left) g ≫ ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom ≫ X.hom) = X.hom
    simp only [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme, Over.mk_hom, Sigma.ι_comp_desc_assoc, Category.id_comp])

noncomputable def target : relation (X := X) (G := G) ⟶ X :=
  Over.homMk (Sigma.desc (fun g => (d.map g).left)) (by
    change (Sigma.desc (fun g => (d.map g).left)) ≫ X.hom =
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom ≫ X.hom
    apply Sigma.hom_ext
    intro g
    simp only [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme, Over.mk_hom, Sigma.ι_comp_desc_assoc, Category.id_comp]
    exact (d.map g).w)

omit [Group G] in
@[simp, reassoc]
theorem inclusion_source (g : G) : inclusion (X := X) g ≫ source = 𝟙 X :=
  Over.OverMorphism.ext (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom g)

@[simp, reassoc]
theorem inclusion_target (g : G) : inclusion (X := X) g ≫ (target d) = d.map g :=
  Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

omit [Group G] in
theorem field_factor (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (f : Over.mk s ⟶ relation (X := X) (G := G)) :
    ∃ g : G, f = (f ≫ source) ≫ inclusion g := by
  obtain ⟨g, hg⟩ := ConstantPointsIs.ConstantPoints.field_factor K f.left
  exact ⟨g, Over.OverMorphism.ext hg⟩

instance relation_etale [Etale X.hom] :
    Etale (relation (X := X) (G := G)).hom :=
  inferInstanceAs (Etale ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom ≫ X.hom))

instance relation_finite [Finite G] [IsFinite X.hom] :
    IsFinite (relation (X := X) (G := G)).hom :=
  inferInstanceAs (IsFinite ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom ≫ X.hom))

theorem jointly_monic [Etale X.hom] :
    JointlyMono₂ (source (X := X) (G := G)) (target d) := by
  constructor
  intro T a b hs ht
  apply IsogenyQuotient.EtaleDetection.Construction.etale_ext_of_field_points
  intro K hK s z
  obtain ⟨g, hg⟩ := field_factor K s (z ≫ a)
  obtain ⟨h, hh⟩ := field_factor K s (z ≫ b)
  have hbase : (z ≫ a) ≫ source = (z ≫ b) ≫ source := by
    simpa only [Category.assoc] using congrArg (fun f => z ≫ f) hs
  have htarget : ((z ≫ a) ≫ source) ≫ d.map g =
      ((z ≫ b) ≫ source) ≫ d.map h := by
    calc
      _ = (z ≫ a) ≫ (target d) := by
        simpa only [Category.assoc, inclusion_target] using
          (congrArg (fun f => f ≫ target d) hg).symm
      _ = (z ≫ b) ≫ (target d) := by
        simpa only [Category.assoc] using congrArg (fun f => z ≫ f) ht
      _ = _ := by
        simpa only [Category.assoc, inclusion_target] using
          congrArg (fun f => f ≫ target d) hh
  rw [← hbase] at htarget
  have hgh := d.free K s ((z ≫ a) ≫ source) g h htarget
  exact hg.trans ((congrArg (fun f => f ≫ inclusion g) hbase).trans
    ((congrArg (fun j => ((z ≫ b) ≫ source) ≫ inclusion j) hgh).trans hh.symm))

noncomputable def symmetry : relation (X := X) (G := G) ⟶ relation (X := X) (G := G) :=
  Over.homMk (Sigma.desc (fun g => (d.map g ≫ inclusion g⁻¹).left)) (by
    change (Sigma.desc (fun g => (d.map g ≫ inclusion g⁻¹).left)) ≫
      (relation (X := X) (G := G)).hom = (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X.left G).hom ≫ X.hom
    apply Sigma.hom_ext
    intro g
    rw [Sigma.ι_comp_desc_assoc]
    exact (d.map g ≫ inclusion g⁻¹).w.trans (inclusion (X := X) g).w.symm)

@[simp, reassoc]
theorem inclusion_symmetry (g : G) : inclusion (X := X) g ≫ (symmetry d) =
    d.map g ≫ inclusion g⁻¹ := Over.OverMorphism.ext (Sigma.ι_comp_desc _ _)

theorem symmetry_source : (symmetry d) ≫ source = (target d) := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro g
  change ((inclusion g ≫ (symmetry d)) ≫ source).left = (inclusion g ≫ (target d)).left
  rw [inclusion_symmetry, inclusion_target, Category.assoc, inclusion_source, Category.comp_id]

theorem symmetry_target : (symmetry d) ≫ (target d) = source := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro g
  change ((inclusion g ≫ (symmetry d)) ≫ (target d)).left = (inclusion g ≫ source).left
  rw [inclusion_symmetry, Category.assoc, inclusion_target, inclusion_source,
    d.map_mul, mul_inv_cancel, d.map_one]

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.FreeConstant.FreeConstantAction
