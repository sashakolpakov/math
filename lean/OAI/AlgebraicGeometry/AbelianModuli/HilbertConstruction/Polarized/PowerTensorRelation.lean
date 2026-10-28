import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Parallelogram
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings

/-! # Power Tensor Relation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual line-bundle power retained in an embedding satisfies the polarized sum-difference tensor identity, also after arbitrary source restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def Line.Bundles.LineBundle.pullbackTensorRelationIso (B : Line.Bundles.LineBundle X) (f g : X ⟶ X)
    (r : ℕ) (e : ((B.pullback f).tensor (B.pullback g)).sheaf ≅ (B.tensorPower r).sheaf)
    (i : Y ⟶ X) :
    ((B.pullback (i ≫ f)).tensor (B.pullback (i ≫ g))).sheaf ≅
      ((B.pullback i).tensorPower r).sheaf :=
  Tensor.Bifunctor.tensorModuleMapIso ((Scheme.Modules.pullbackComp i f).symm.app B.sheaf)
      ((Scheme.Modules.pullbackComp i g).symm.app B.sheaf) ≪≫
    ((B.pullback f).tensorBaseChangeIso i (B.pullback g)).symm ≪≫
    (Scheme.Modules.pullback i).mapIso e ≪≫ B.powerBaseChangeIso i r

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def Moduli.Isomorphisms.LevelPreservingIso.embeddingPower_sum_difference_iso (e : Moduli.Isomorphisms.LevelPreservingIso A A)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) :
    ((E.power.pullback (e.abelian.hom * (𝟙 A.abelian.scheme)).left).tensor
      (E.power.pullback (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)).sheaf ≅
      (E.power.tensorPower 4).sheaf := by
  let a := (E.isPower.unique (A.graphBundle.tensorPower_isTensorPower E.degree)).some
  exact Tensor.Bifunctor.tensorModuleMapIso ((Scheme.Modules.pullback _).mapIso a)
      ((Scheme.Modules.pullback _).mapIso a) ≪≫
    e.graphPower_sum_difference_iso A E.degree ≪≫ (TensorPower.Maps.tensorPowerFunctor _ 4).mapIso a.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
