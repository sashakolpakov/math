import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.MultiplicativeFactor
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupTensorIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor

/-! # Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Splitting.CM

noncomputable section

/-! The original ordinary polarized abelian torsion scheme has the
full multiplicative-etale splitting at every finite level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) (q : ℕ) [Fact q.Prime] [CharP k q]

theorem splitting
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) :
    Nonempty (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (@Grp.mk _ _ _ (A.abelian.torsionScheme (q ^ n))
        (A.abelian.torsionScheme_group (q ^ n))) q n g g) := by
  let : IsFinite (A.abelian.torsionScheme (q ^ n)).hom :=
    TorsionFinite.CM.torsion_finite A.abelian q hordinary n
  let Tor : Grp (Over (Spec (.of k))) := Grp.mk (A.abelian.torsionScheme (q ^ n))
  let : IsFinite Tor.X.hom :=
    TorsionFinite.CM.torsion_finite A.abelian q hordinary n
  let : IsCommMonObj Tor.X := A.abelian.torsionScheme_commutative (q ^ n)
  obtain ⟨m⟩ := MultiplicativeFactor.CM.multiplicative_factor A q hordinary n
  obtain ⟨e⟩ := AllTorsionCoordinates.CM.coordinates_all
    A.abelian.scheme q g hordinary n
  let u : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q n g ≃*
      TorsionCoordinateMaps.CM.Criterion.coordinates q n g := MulEquiv.ulift
  let p := (u.trans e).trans ((A.abelian.torsionSchemeYonedaIso (q ^ n)).app
    (.op (Over.mk (𝟙 (Spec (.of k)))))).groupIsoToMulEquiv.symm
  let t : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q n g ≅ Finite.GroupDecomposition.CM.pointGroup Tor :=
    AbelianScheme.FrobeniusKernel.EtaleGroupFunctor.Construction.etaleGroupIso (Spec (.of k)) p
  exact ⟨(Finite.GroupDecomposition.CM.decomposition Tor).symm ≪≫
    GroupTensorIso.CM.left (Finite.GroupDecomposition.CM.pointGroup Tor) (Finite.GroupDecomposition.CM.neutralPart Tor)
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n g) m ≪≫
    GroupTensorIso.CM.right (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q n g)
      (Finite.GroupDecomposition.CM.pointGroup Tor) (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q n g) t.symm⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Splitting.CM
