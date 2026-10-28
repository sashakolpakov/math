import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Quadratic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Parallelogram
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings

/-! # Embedding Power Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual embedding power of the canonical polarized bundle retains its quadratic pullback law under multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def Line.Bundles.LineBundle.pullbackPowerIdentityIso (L : Line.Bundles.LineBundle X) (f : X ⟶ X) (r : ℕ)
    (e : (L.pullback f).sheaf ≅ (L.tensorPower r).sheaf) (d : ℕ) :
    ((L.tensorPower d).pullback f).sheaf ≅ ((L.tensorPower d).tensorPower r).sheaf :=
  L.powerBaseChangeIso f d ≪≫ (TensorPower.Maps.tensorPowerFunctor X d).mapIso e ≪≫ L.tensorPowersCommuteIso r d

def PolarizationData.PolarizedAbelianWithFullLevel.embeddingPower_multiplication_iso
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) (n : ℕ) :
    (E.power.pullback (A.abelian.multiplication n).left).sheaf ≅
      (E.power.tensorPower (n * n)).sheaf := by
  let e := (E.isPower.unique (A.graphBundle.tensorPower_isTensorPower E.degree)).some
  exact (Scheme.Modules.pullback (A.abelian.multiplication n).left).mapIso e ≪≫
    A.graphBundle.pullbackPowerIdentityIso (A.abelian.multiplication n).left (n * n)
      (A.graphBundle_multiplication_iso n).some E.degree ≪≫
    (TensorPower.Maps.tensorPowerFunctor _ (n * n)).mapIso e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
