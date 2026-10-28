import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Source
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.SingleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.ClassCoordinates

/-! # Source -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Source.Comparison

noncomputable section

/-! The original point-class comparison in degree c+g has the exact
source single-sheaf image after its retained degree cast. All cover
isomorphisms follow from the original point-parameter geometry. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.RelativeGeometry
variable {Y X Z T S : Scheme.{0}} [X.IsSeparated] [Z.IsSeparated]
  (f : Y ⟶ X) (i : X ⟶ Z) [IsClosedImmersion i] (π : Z ⟶ S)
  (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Z.Opens) (hU : IsAffineOpen U) (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {c g : ℕ} (s : Fin c → Γ(Z,U)) (t : Fin g → Γ(Z,U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U,hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  {κ : Type} [LinearOrder κ] (V : κ → Z.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))
  (N : Y.Modules) [((Scheme.Modules.pushforward f).obj N).IsQuasicoherent]

abbrev image := PrincipalSource.OpenRestriction.image f i N
abbrev family := Fraction.family U t
abbrev localTotal := PrincipalSource.ClassCoordinates.total f i U hU N t c

local instance image_qc : (image f i N).IsQuasicoherent :=
  AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
local instance single_qc (k : ℕ) : (((single Z.Modules (.up ℕ) c).obj (image f i N)).X k).IsQuasicoherent :=
  QuasicoherentTruncation.single (image f i N) c k

include hs hst in
private theorem relative_isIso (q : ℕ) :
    IsIso (RelativeCech.Refinement.homology (Principal.RelativeConcentration.ambient U hU)
      (RelativeGeometry.complementary i s₀) (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t)
      (Principal.NestedPushforward.original f i N c) q) :=
  RelativeGeometry.right_isIso i s₀ U hU s t hs hst ((single Z.Modules (.up ℕ) c).obj (image f i N)) c
    (fun k hk => exactAt_single_obj (.up ℕ) c (image f i N) k hk)
    ((Scheme.Modules.pushforward f).obj N) (singleObjHomologySelfIso (.up ℕ) c (image f i N)) q

def ordinaryMap (q : ℕ) (hq : q=g+c) :=
  (Principal.AdditiveSections.forgetScalars U).map
    (Principal.SingleModuleCoordinates.moduleCoordinates U hU (image f i N) c (family U t) g q hq).hom ≫
      SingleCoordinates.coefficientComparison π i s₀ U hU hcontains s t hs hst V hV haV
        ((Scheme.Modules.pushforward f).obj N) c q hq

abbrev sourceOutput := PrincipalReference.Source.ReferenceComparison.sourceOutput (c := c) (g := g) f i π V N

def sourceComparison := by
  let := relative_isIso f i s₀ U hU s t hs hst N (g+c)
  exact PrincipalReference.Source.ReferenceComparison.sourceComparison f i U hU (family U t) (s₀ ≫ i) hcontains
    (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.left i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t) V hV haV N c g

def cast (q : ℕ) (hq : q=g+c) : (localTotal (c := c) f i U hU t N).homology q ⟶
    (localTotal (c := c) f i U hU t N).homology (g+c) :=
  eqToHom (congrArg (fun j => (localTotal (c := c) f i U hU t N).homology j) hq)

theorem degree (q : ℕ) (hq : q=g+c) :
    ordinaryMap f i π s₀ U hU hcontains s t hs hst V hV haV N q hq =
      (Principal.AdditiveSections.forgetScalars U).map (cast (c := c) f i U hU t N q hq) ≫
        ordinaryMap f i π s₀ U hU hcontains s t hs hst V hV haV N (g+c) rfl := by
  subst q
  simp only [cast, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]

theorem comparison (q : ℕ) (hq : q=g+c) :
    ordinaryMap f i π s₀ U hU hcontains s t hs hst V hV haV N q hq ≫ sourceOutput (c := c) (g := g) f i π V N =
    (Principal.AdditiveSections.forgetScalars U).map (cast (c := c) f i U hU t N q hq) ≫
      (PrincipalSource.SupportedCoordinates.wideIso f i U hU (family U t) N c (g+c)).hom ≫
      sourceComparison f i s₀ U hU hcontains s t hs hst V hV haV N := by
  subst q
  simp only [cast, eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp]
  let := relative_isIso f i s₀ U hU s t hs hst N (g+c)
  have h := PrincipalReference.Source.ReferenceComparison.comparison f i π U hU (family U t) (s₀ ≫ i) hcontains
    (RelativeGeometry.common i s₀ U hU t) (RelativeGeometry.left i s₀ U hU t) (RelativeGeometry.right i s₀ U hU t) V hV haV N c g
  simp only [ordinaryMap, SingleCoordinates.coefficientComparison,
    PrincipalReference.Source.ReferenceComparison.originalMap,
    PrincipalSource.PushforwardCoordinates.localCoordinates, Category.assoc] at h ⊢
  convert h using 1; rfl

theorem comparison_apply (x : (localTotal (c := c) f i U hU t N).homology (c+g)) :
    sourceOutput (c := c) (g := g) f i π V N
      (ordinaryMap f i π s₀ U hU hcontains s t hs hst V hV haV N (c+g) (Nat.add_comm c g) x) =
    sourceComparison f i s₀ U hU hcontains s t hs hst V hV haV N
      (PrincipalSource.ClassCoordinates.wideClass f i U hU N t c x) := by
  have h := comparison f i π s₀ U hU hcontains s t hs hst V hV haV N (c+g) (Nat.add_comm c g)
  have hx := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply] at hx
  convert hx using 1; rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Source.Comparison
