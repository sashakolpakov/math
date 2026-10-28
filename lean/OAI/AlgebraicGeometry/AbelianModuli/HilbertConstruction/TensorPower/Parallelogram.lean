import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphParallelogram
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Parallelogram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A tensor-product identity for two pullbacks persists through every tensor power. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def Line.Bundles.LineBundle.tensorPowersCommuteIso (L : Line.Bundles.LineBundle X) (a b : ℕ) :
    ((L.tensorPower a).tensorPower b).sheaf ≅ ((L.tensorPower b).tensorPower a).sheaf :=
  (L.tensorPowerComposeIso b a).symm ≪≫
    eqToIso (congrArg (fun n => (L.tensorPower n).sheaf) (Nat.mul_comm b a)) ≪≫
    L.tensorPowerComposeIso a b

def Line.Bundles.LineBundle.pullbackTensorPowerIdentityIso (L : Line.Bundles.LineBundle Y) (f g : X ⟶ Y)
    (M : Line.Bundles.LineBundle X) (r : ℕ)
    (e : ((L.pullback f).tensor (L.pullback g)).sheaf ≅ (M.tensorPower r).sheaf) (d : ℕ) :
    (((L.tensorPower d).pullback f).tensor ((L.tensorPower d).pullback g)).sheaf ≅
      ((M.tensorPower d).tensorPower r).sheaf :=
  Tensor.Bifunctor.tensorModuleMapIso (L.powerBaseChangeIso f d) (L.powerBaseChangeIso g d) ≪≫
    ((L.pullback f).tensorPowerTensorIso (L.pullback g) d).symm ≪≫
    (TensorPower.Maps.tensorPowerFunctor X d).mapIso e ≪≫ M.tensorPowersCommuteIso r d

def Moduli.Isomorphisms.LevelPreservingIso.graphPower_sum_difference_iso
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (e : Moduli.Isomorphisms.LevelPreservingIso A A) (d : ℕ) :
    (((A.graphBundle.tensorPower d).pullback (e.abelian.hom * (𝟙 A.abelian.scheme)).left).tensor
      ((A.graphBundle.tensorPower d).pullback (e.abelian.hom * (𝟙 A.abelian.scheme)⁻¹).left)).sheaf ≅
      ((A.graphBundle.tensorPower d).tensorPower 4).sheaf :=
  A.graphBundle.pullbackTensorPowerIdentityIso _ _ A.graphBundle 4
    (e.graphBundle_sum_difference_iso A) d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
