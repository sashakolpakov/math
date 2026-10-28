import OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechZeroIntersections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplementComplex

/-! # Supported Ordered Cech Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechForget.Abelian

noncomputable section

/-! The original supported-section edge forgets to the literal supported
inclusion. If positive intersections vanish, this identifies the edge
with the inverse of support-forgetting, including the canonical global lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechEdge.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem column_cancel {A : Type*} [Category A] {N B D T : A}
    (s : N ⟶ B) (e : D ≅ B) (i : D ⟶ T) (p : T ⟶ D) (h : i ≫ p = 𝟙 D) :
    ((s ≫ e.inv) ≫ i) ≫ (p ≫ e.hom) = s := by
  simp only [Category.assoc]
  rw [← Category.assoc i p e.hom, h, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem inverse_factor {A : Type*} [Category A] {N B D : A}
    (a : N ⟶ D) (b : N ⟶ B) (e : D ≅ B) (h : a ≫ e.hom = b) :
    a = b ≫ e.inv := by
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

universe u
variable (D : Type (u+1)) [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  (X : TopCat.{u}) {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Opens X)

local notation "V" => F.obj (⊤_ C)

variable (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
  D) ℕ) (hO : ∀ i, F.obj (U i) ≤ O)

local instance total_exists : (SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

local instance augmented_total_exists :
    (AugmentedOrdered.CechFunctor.bicomplex U (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K)).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

abbrev inclusion := Supported.ZeroComplementComplex.localInclusion O (F.obj (⊤_ C)) K

theorem map_forget : SupportedOrderedCechEdge.Abelian.map D X F U O K hO ≫
    AugmentedOrdered.CechForget.forgetSupport U (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K) =
    inclusion D X F O K := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact column_cancel
    ((Supported.SectionsExcision.inclusion (F.obj (⊤_ C))
      (F.obj (⊤_ C) ⊓ O) inf_le_left).app (K.X n))
    (AugmentedOrdered.CechZero.zeroIso U (F.op ⋙ (K.X n).obj))
    ((SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).ιTotal (.up ℕ) n 0 n rfl)
    ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (bicomplex D X F U K)) n 0 n)
    (by
      change (SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).ιTotal (.up ℕ) n 0 n rfl ≫
        (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (bicomplex D X F U K)) n 0 n =
        𝟙 (((SupportedOrderedCechEdge.Abelian.bicomplex D X F U K).X n).X 0)
      simpa only [Nat.add_zero] using
        (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_πTotalUpNat_self (bicomplex D X F U K)) n 0)

variable (hzero : ∀ p q, 0 < q → ∀ a : AugmentedOrdered.Cech.Index ι q,
    IsZero (((SupportedOrderedCechEdge.Abelian.presheafComplex D X F K).X p).obj
      (op ((AugmentedOrdered.Cech.formal U q).obj a))))

abbrev forgetIso := AugmentedOrdered.CechZeroIntersections.iso U
  (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K) hzero

theorem factorization : SupportedOrderedCechEdge.Abelian.map D X F U O K hO =
    inclusion D X F O K ≫ (forgetIso D X F U K hzero).inv :=
  inverse_factor _ _ (forgetIso D X F U K hzero) (map_forget D X F U O K hO)

theorem homology_factorization (q : ℕ) :
    HomologicalComplex.homologyMap (SupportedOrderedCechEdge.Abelian.map D X F U O K hO) q =
    HomologicalComplex.homologyMap (inclusion D X F O K) q ≫
      (HomologicalComplex.homologyMapIso (forgetIso D X F U K hzero) q).inv := by
  let H := HomologicalComplex.homologyFunctor D (.up ℕ) q
  exact (congrArg H.map (factorization D X F U O K hO hzero)).trans (H.map_comp _ _)

variable (hglobal : ∀ q, IsZero ((K.X q).obj.obj (op O)))

theorem global_lift_forget :
    (Supported.ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hglobal ≫
      SupportedOrderedCechEdge.Abelian.map D X F U O K hO) ≫
      AugmentedOrdered.CechForget.forgetSupport U (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K) =
    Supported.ZeroComplementComplex.restrictionMap (F.obj (⊤_ C)) K :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => Supported.ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hglobal ≫ q)
      (map_forget D X F U O K hO)).trans
      (Supported.ZeroComplementComplex.lift_inclusion O (F.obj (⊤_ C)) K hglobal))

theorem global_lift_factorization :
    Supported.ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hglobal ≫
      SupportedOrderedCechEdge.Abelian.map D X F U O K hO =
    Supported.ZeroComplementComplex.restrictionMap (F.obj (⊤_ C)) K ≫
      (forgetIso D X F U K hzero).inv :=
  inverse_factor _ _ (forgetIso D X F U K hzero) (global_lift_forget D X F U O K hO hglobal)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechForget.Abelian
