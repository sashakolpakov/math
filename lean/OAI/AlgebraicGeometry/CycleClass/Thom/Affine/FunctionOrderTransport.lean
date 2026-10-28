import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.GenericFieldComposition

/-! # Function Order Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.FunctionOrderTransport.Constructions

noncomputable section

/-! Actual affine rational functions commute with generic-stalk maps.
Ring isomorphisms therefore preserve their original scheme orders. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GenericFieldComposition.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RationalOrderTransport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]

local instance (A : Type u) [CommRing A] [IsDomain A] : Nonempty (⊤ : (Spec (.of A)).Opens) :=
  ⟨⟨genericPoint (Spec (.of A)), Opens.mem_top _⟩⟩

theorem genericFieldMap_affineFunction (f : R →+* S)
    (hη : (Spec.map (CommRingCat.ofHom f)) (genericPoint (Spec (.of S))) = genericPoint (Spec (.of R))) (a : R) :
    RationalOrderTransport.Constructions.genericFieldMap (Spec.map (CommRingCat.ofHom f)) hη (PrincipalSchemeOrder.Constructions.affineFunction R a) = PrincipalSchemeOrder.Constructions.affineFunction S (f a) := by
  have h := GenericFieldComposition.Constructions.genericFieldMap_germ_appLE (Spec.map (CommRingCat.ofHom f)) hη ⊤ ⊤ (by simp)
  have hg := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of R)).inv a)
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) a
  exact hg.trans (congrArg ((Spec (.of S)).germToFunctionField ⊤) he.symm)

variable [IsNoetherianRing R] [IsNoetherianRing S]

theorem ord_affineFunction_equiv (e : R ≃+* S) (a : R) (q : Spec (.of S)) :
    (Spec (.of S)).ord (PrincipalSchemeOrder.Constructions.affineFunction S (e a)) q =
      (Spec (.of R)).ord (PrincipalSchemeOrder.Constructions.affineFunction R a) ((Spec.map e.toCommRingCatIso.hom) q) := by
  let i := Spec.map e.toCommRingCatIso.hom
  have he := genericFieldMap_affineFunction R S e.toRingHom (genericPoint_eq_of_isOpenImmersion i) a
  exact (congrArg (fun g => (Spec (.of S)).ord g q) he).symm.trans
    (RationalOrderTransport.Constructions.ord_openImmersion i (PrincipalSchemeOrder.Constructions.affineFunction R a) q)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.FunctionOrderTransport.Constructions
