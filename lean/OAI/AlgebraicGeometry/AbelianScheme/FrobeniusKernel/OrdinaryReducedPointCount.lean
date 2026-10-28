import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryEtaleTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantGroupPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Ordinary Reduced Point Count -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryReducedPointCount.Construction

noncomputable section

section

/-! A reduced connected test scheme sees precisely the constant factor
of an ordinary q-torsion splitting. This includes every extension field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
  {G : Grp (Over (Spec (.of k)))} {d r : ℕ} (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q 1 d r)
  (T : Over (Spec (.of k))) [IsReduced T.left]

def ordinaryReducedPointsEquiv : (T ⟶ G.X) ≃ (T ⟶ (OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r).X) := by
  let M := OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 d
  let E := OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 r
  letI : Unique (T ⟶ M.X) := {
    default := 1
    uniq x := ReducedHeightOneMaps.Construction.map_from_reduced_of_trivial_frobenius q (Fact.out : q.Prime)
      (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) x
      (Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k d) }
  exact ((Iso.homCongr (Iso.refl T) ((Grp.forget _).mapIso e)).trans
    (homEquivToProd (X := M.X) (Y := E.X) (Z := T))).trans (Equiv.uniqueProd (T ⟶ E.X) (T ⟶ M.X))

def etaleConnectedPointsEquiv {S : Scheme} (D : Type) [Group D]
    (T : Over S) [PreconnectedSpace T.left] (t : T.left) :
    (T ⟶ (EtaleSubgroups.Construction.etaleGroupScheme S D).X) ≃ D :=
  ((EtaleSubgroups.Construction.etaleGroupPointIso S D).app (.op T)).groupIsoToMulEquiv.toEquiv.trans
    (HodgeConjecture.HeckeCycles.ConstantGroupPoints.CM.constantEquiv T.left D t).toEquiv.symm

include e in
theorem ordinaryReducedPoints_card [PreconnectedSpace T.left] (t : T.left) :
    Nat.card (T ⟶ G.X) = q ^ r := by
  have h := Nat.card_congr ((ordinaryReducedPointsEquiv q k e T).trans
    (etaleConnectedPointsEquiv (OrdinaryBlocks.Construction.OrdinaryBlockLabels.{0} q 1 r) T t))
  simpa only [OrdinaryBlocks.Construction.OrdinaryBlockLabels, Nat.card_eq_fintype_card, Fintype.card_ulift, Fintype.card_multiplicative,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, pow_one] using h

end

/-! An actual full ordinary torsion splitting gives the same etale
point count after every field extension, through native torsion base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k F : Type} [Field k] [Field F]
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (q : ℕ) [Fact q.Prime] [CharP k q] {d r : ℕ}
  (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
    (@Grp.mk _ _ _ (A.torsionScheme (q ^ 1)) (A.torsionScheme_group (q ^ 1))) q 1 d r)

include e in
theorem splitTorsion_torsionCard_fieldExtension (f : Spec (.of F) ⟶ Spec (.of k)) :
    Nat.card ((A.pullback f).torsionPoints q (Over.mk (𝟙 (Spec (.of F))))) = q ^ r := by
  let T := (Over.map f).obj (Over.mk (𝟙 (Spec (.of F))))
  have : IsReduced T.left := inferInstanceAs (IsReduced (Spec (.of F)))
  have : PreconnectedSpace T.left := inferInstanceAs (PreconnectedSpace (Spec (.of F)))
  have h : Nat.card ((A.pullback f).torsionPoints (q ^ 1) (Over.mk (𝟙 (Spec (.of F))))) = q ^ r :=
    (Nat.card_congr ((A.torsionBaseChangeEquiv f (Over.mk (𝟙 (Spec (.of F)))) (q ^ 1)).toEquiv.trans
      (A.torsionSchemePointsEquiv (q ^ 1) T).symm)).trans
      (ordinaryReducedPoints_card q k e T (IsLocalRing.closedPoint F))
  simpa only [pow_one] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryReducedPointCount.Construction
