import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedGlobalData
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SupportedGlobalCoefficients

/-! # Principal Supported Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSupportedGlobal

noncomputable section

/-! The actual additive principal-to-global target map agrees with
the original supported crystalline map after its canonical coefficients. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (U : X.left.affineOpens)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) (a : Fin g → Γ(X.left,U.val))

abbrev opens := SupportedGlobalData.opens p k n X U
abbrev family := SupportedGlobalData.family p k n X U g a
abbrev linear := CechIso.ResolutionGlobal.presheaf p k n X Y f I
abbrev target := AdditiveGlobal.target p k n X Y f I
abbrev forget := AdditiveTop.Comparison.forget p k
abbrev localComplex :=
  ((AugmentedCech.AmbientTotal.restriction (opens p k n X U)).mapHomologicalComplex
    (.up ℕ)).obj (linear p k n X Y f I)

local instance tuple_preserves (d : ℕ) (z : Fin (d+1) → ULift (Fin g)) :
    PreservesLimit (Discrete.functor (family p k n X U g a ∘ z)) (opens p k n X U) :=
  AffinePrincipal.Products.preserves X.left U.val U.property (family p k n X U g a ∘ z)

def localIso (q : ℕ) := AugmentedCech.CoefficientTotal.homologyIso
  (family p k n X U g a) (forget p k) (localComplex p k n X Y f U I) q

variable {κ ν μ ρ : Type}
  [LinearOrder κ] [LinearOrder ν] [LinearOrder μ] [LinearOrder ρ]
  (B : κ → X.left.Opens) (J : ν → X.left.Opens)
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk (ULift (Fin g))
    ((opens p k n X U).obj ∘ family p k n X U g a))
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ B)
  (V : μ → X.left.Opens) (hV : iSup V = ⊤) (T : ρ → X.left.Opens)
  (l : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk (WithBot κ)
    (RelativeCech.Intersections.cover
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B))
  (t : FormalCoproduct.mk ρ T ⟶ FormalCoproduct.mk μ V)
  (O : X.left.Opens)
  (hO : ∀ j, (opens p k n X U).obj (family p k n X U g a j) ≤ O)
  (hB : ∀ j, B j ≤ O)
  (hcover : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊓ O ≤
    ⨆ j, (opens p k n X U).obj (family p k n X U g a j))
  (hglobal : (opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U)) ⊔ O = ⊤)
  (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology
    ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
    (linear p k n X Y f I) q)]
  [IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (linear p k n X Y f I)) q)]

def globalValue :
    ((AugmentedOrdered.CechFunctor.bicomplex (family p k n X U g a)
      (AugmentedCech.CoefficientTotal.mapped (forget p k)
        (localComplex p k n X Y f U I))).total (.up ℕ)).homology q ⟶
    (forget p k).obj (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
        (Witt.Crystalline.wittStructureMap p k Y) n q)) := by
  letI : IsIso (RelativeCech.Refinement.homology
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
      (target p k n X Y f I) q) :=
    Presheaf.CoverCoefficients.relative_isIso (forget p k) (linear p k n X Y f I)
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s q
  letI : IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t
      (target p k n X Y f I)) q) :=
    Presheaf.CoverCoefficients.ordered_isIso (forget p k) (linear p k n X Y f I) V T t q
  letI := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I V hV q
  exact Principal.PresheafCover.Comparison.comparison (opens p k n X U)
      (family p k n X U g a) B J r s V T l t (target p k n X Y f I) q ≫
    inv (homologyMap (Presheaf.OrderedCechEdge.edge V (target p k n X Y f I)) q) ≫
      (AdditiveGlobal.globalHomologyIso p k n X Y f I q).hom

include hB in
omit [Fintype k] [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem coordinates :
    (localIso p k n X Y f U I g a q).hom ≫
      globalValue p k n X Y f U I g a B J r s V hV T l t q =
    (forget p k).map
      (SupportedGlobalData.forgetSupport p k n X Y f U I g a O hO hcover hglobal q ≫
        (CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q).hom) := by
  let : ∀ (d : ℕ) (z : Fin (d+1) → ULift (Fin g)),
      PreservesLimit (Discrete.functor (family p k n X U g a ∘ z)) (opens p k n X U) :=
    fun _ z => AffinePrincipal.Products.preserves X.left U.val U.property
      (family p k n X U g a ∘ z)
  let := AdditiveGlobal.ResolutionFlasque.linear_edge_isIso p k n X Y f I V hV q
  let L := Relative.SupportedExtension.underlying.{1,0,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) X.left.toTopCat
    (ModelSheafComparison.target p k n X Y f I)
  let : IsIso (RelativeCech.Refinement.homology
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s L q) := by
    change IsIso (RelativeCech.Refinement.homology
      ((opens p k n X U).obj (⊤_ (PrincipalFrame.Index X.left U))) B J s
      (linear p k n X Y f I) q)
    infer_instance
  let : IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t L) q) := by
    change IsIso (homologyMap (OrderedCech.Refinement.totalMap V T t (linear p k n X Y f I)) q)
    infer_instance
  let : IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V L) q) := by
    change IsIso (homologyMap (Presheaf.OrderedCechEdge.edge V (linear p k n X Y f I)) q)
    infer_instance
  have h := Principal.SupportedGlobalCoefficients.with_target.{1,0,2}
    (Crystalline.ExactRestriction.Coeff (B := WittVector p k)) X.left.toTopCat
    (ModelSheafComparison.target p k n X Y f I)
    (opens p k n X U) (family p k n X U g a) B J r s V T l t O hO hB hglobal q hcover
    (SupportedGlobalData.exactAt_succ p k n X Y f U I g a) (forget p k) _
    (CechIso.ResolutionGlobal.globalHomologyIso p k n X Y f I q).hom
  simp only [globalValue, AdditiveGlobal.globalHomologyIso,
    Iso.trans_hom, Functor.mapIso_hom]
  convert h using 1 <;> rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSupportedGlobal
