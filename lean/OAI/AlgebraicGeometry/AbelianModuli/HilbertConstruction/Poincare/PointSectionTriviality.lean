import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PointBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.SectionFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.InverseSectionFrames

/-! # Point Section Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A nonzero global section of an actual Poincare point bundle forces that bundle to be trivial. Translation moves a section frame to the origin; inversion supplies the paired frame. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
variable (f : 𝟙_ (Over (Spec (.of K))) ⟶ D.abelian.scheme)

theorem Dual.Data.DualAbelianData.poincarePointBundle_trivial_of_nonzero_section
    (s : Line.Bundles.structureModule A.scheme.left ⟶ (D.poincarePointBundle f).sheaf) (hs : s ≠ 0) :
    Nonempty ((D.poincarePointBundle f).sheaf ≅ Line.Bundles.structureModule A.scheme.left) := by
  have : IsReduced A.scheme.left := A.reduced_overField
  have : ConnectedSpace A.scheme.left := A.connected_overField
  let L := D.poincarePointBundle f
  obtain ⟨a₀, ha₀, haFrame⟩ := L.exists_rational_frame_of_ne_zero A.scheme.hom s hs
  let a : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme := Over.homMk a₀ ha₀
  let z : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme := η[A.scheme]
  let T := A.basePointTranslation a
  let e : (Scheme.Modules.pullback T.left).obj L.sheaf ≅ L.sheaf :=
    D.poincarePointBundle_translationIso f a
  let s₀ : Line.Bundles.structureModule A.scheme.left ⟶ L.sheaf := Ample.LineBundles.pullbackSection T.left s ≫ e.hom
  have hzT : z ≫ T = a := by
    change (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) ≫
      ((toUnit A.scheme ≫ a) * 𝟙 A.scheme) = a
    simp only [MonObj.comp_mul, comp_toUnit_assoc, toUnit_unit, Category.id_comp,
      Category.comp_id, mul_one]
  have hzT' : z.left ≫ T.left = a₀ := congrArg Over.Hom.left hzT
  have htranslated : IsIso (Ample.LineBundles.pullbackSection z.left (Ample.LineBundles.pullbackSection T.left s)) := by
    apply (Section.Nonvanishing.isIso_pullbackSection_comp_iff T.left z.left s).mpr
    rw [hzT']
    exact haFrame
  have hs₀ : IsIso (Ample.LineBundles.pullbackSection z.left s₀) := by
    change IsIso ((Line.Bundles.structureModulePullbackIso z.left).inv ≫
      (Scheme.Modules.pullback z.left).map (Ample.LineBundles.pullbackSection T.left s ≫ e.hom))
    rw [Functor.map_comp, ← Category.assoc]
    change IsIso (Ample.LineBundles.pullbackSection z.left (Ample.LineBundles.pullbackSection T.left s) ≫
      (Scheme.Modules.pullback z.left).map e.hom)
    infer_instance
  let h : A.scheme ⟶ A.scheme := (𝟙 A.scheme)⁻¹
  let M := L.pullback h.left
  let t : Line.Bundles.structureModule A.scheme.left ⟶ M.sheaf := Ample.LineBundles.pullbackSection h.left s₀
  have hzH : z ≫ h = z := by
    change (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A.scheme) ≫ (𝟙 A.scheme)⁻¹ = 1
    simp only [GrpObj.comp_inv, Category.comp_id, inv_one]
  have ht : IsIso (Ample.LineBundles.pullbackSection z.left t) := by
    apply (Section.Nonvanishing.isIso_pullbackSection_comp_iff h.left z.left s₀).mpr
    rw [show z.left ≫ h.left = z.left from congrArg Over.Hom.left hzH]
    exact hs₀
  have hframes := Tensor.InverseSectionFrames.tensorInverse_sections_frames_of_rationalFiber A.scheme.hom z.left z.w
    L M (D.poincarePointBundle_inversePairingIso f) s₀ t
  have : IsIso s₀ := hframes.1
  exact ⟨(asIso s₀).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
