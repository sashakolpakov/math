import OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtExtensions

/-! # Short Exact Transport -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport.Construction

noncomputable section

/-!
# Completion: changing the endpoints of an actual extension along isomorphisms
-/

open _root_.CategoryTheory Limits Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {A B : C} (a : S.X₁ ≅ A) (b : S.X₃ ≅ B)

/-- Change both endpoints of a short exact complex, retaining its middle object. -/
def endpointTransportComplex : ShortComplex C :=
  ShortComplex.mk (a.inv ≫ S.f) (S.g ≫ b.hom) (by simp [Category.assoc])

/-- The transported complex is isomorphic to the original actual complex. -/
def endpointTransportIso : S ≅ endpointTransportComplex S a b :=
  ShortComplex.isoMk a (Iso.refl _) b (by simp [endpointTransportComplex])
    (by simp [endpointTransportComplex])

theorem endpointTransport_shortExact (hS : S.ShortExact) :
    (endpointTransportComplex S a b).ShortExact :=
  ShortComplex.shortExact_of_iso (endpointTransportIso S a b) hS

variable [HasExt.{w} C]

/-- Endpoint transport changes the extension class by the actual pre- and postcomposition maps. -/
theorem endpointTransport_extClass (hS : S.ShortExact) :
    (endpointTransport_shortExact S a b hS).extClass =
      ((Ext.mk₀ b.inv).comp hS.extClass (zero_add 1)).comp (Ext.mk₀ a.hom) (add_zero 1) := by
  have h := ShortComplex.ShortExact.extClass_naturality hS
    (endpointTransport_shortExact S a b hS) (endpointTransportIso S a b).hom
  have hh := congrArg (fun z => (Ext.mk₀ b.inv).comp z (zero_add 1)) h
  simpa only [endpointTransportIso, ShortComplex.isoMk_hom_τ₁, ShortComplex.isoMk_hom_τ₃,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, b.inv_hom_id, Ext.mk₀_id_comp,
    ← Ext.comp_assoc_of_third_deg_zero] using hh.symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ShortExactTransport.Construction
