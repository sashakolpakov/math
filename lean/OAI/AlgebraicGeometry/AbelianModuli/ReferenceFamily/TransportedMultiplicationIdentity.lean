import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedProduct.ReducedGroupMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointedTensorIsomorphism

/-! # Transported Multiplication Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TransportedMultiplicationIdentity

section

/-! Transporting multiplication through an actual product carrier
isomorphism gives two maps on the same constant product family.
Their reductions agree before any multiplication compatibility is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [G.Monoidal]
    (X : D) [GrpObj X] (e : X ≅ F.obj (G.obj X))

def productMultiplicationTransportIso : F.obj (G.obj X ⊗ G.obj X) ≅ X ⊗ X :=
  (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).symm ≪≫ (e ⊗ᵢ e).symm

def productMultiplicationTransport : F.obj (G.obj X ⊗ G.obj X) ⟶ F.obj (G.obj X) :=
  (productMultiplicationTransportIso F G X e).hom ≫ μ[X] ≫ e.hom

def productMultiplicationReference : F.obj (G.obj X ⊗ G.obj X) ⟶ F.obj (G.obj X) :=
  (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv ≫ μ[F.obj (G.obj X)]

theorem productMultiplicationReference_transport :
    (productMultiplicationTransportIso F G X e).hom ≫ ((e.hom ⊗ₘ e.hom) ≫ μ[F.obj (G.obj X)]) =
      productMultiplicationReference F G X := by
  change ((Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv ≫ (e ⊗ᵢ e).inv) ≫
    ((e ⊗ᵢ e).hom ≫ μ[F.obj (G.obj X)]) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

theorem productMultiplicationTransport_reduction (n : F ⋙ G ≅ 𝟭 C)
    (he : NormalizedDual.OpenProductData.NormalizesProductFiber F G n e) :
    G.map (productMultiplicationTransport F G X e) = G.map (productMultiplicationReference F G X) := by
  have h := NormalizedProduct.ReducedGroupMap.normalizedProduct_reduced_multiplication F G n X e he
  calc
    G.map (productMultiplicationTransport F G X e) =
        G.map (productMultiplicationTransportIso F G X e).hom ≫ G.map (μ[X] ≫ e.hom) := G.map_comp _ _
    _ = G.map (productMultiplicationTransportIso F G X e).hom ≫
        G.map ((e.hom ⊗ₘ e.hom) ≫ μ[F.obj (G.obj X)]) := congrArg (fun f => G.map _ ≫ f) h
    _ = G.map ((productMultiplicationTransportIso F G X e).hom ≫
        ((e.hom ⊗ₘ e.hom) ≫ μ[F.obj (G.obj X)])) := (G.map_comp _ _).symm
    _ = G.map (productMultiplicationReference F G X) := congrArg G.map (productMultiplicationReference_transport F G X e)

theorem productMultiplication_eq_of_transport
    (he : productMultiplicationTransport F G X e = productMultiplicationReference F G X) :
    μ[X] ≫ e.hom = (e.hom ⊗ₘ e.hom) ≫ μ[F.obj (G.obj X)] := by
  apply (cancel_epi (productMultiplicationTransportIso F G X e).hom).mp
  exact he.trans (productMultiplicationReference_transport F G X e).symm

end

/-! For a pointed carrier isomorphism, transported and original
multiplication agree on the actual identity section. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Braided] [G.Braided]
    (X : D) [GrpObj X] (e : X ≅ F.obj (G.obj X))

theorem productMultiplicationTransportIso_point (he : η[X] ≫ e.hom = η[F.obj (G.obj X)]) :
    η[F.obj (G.obj X ⊗ G.obj X)] ≫ (productMultiplicationTransportIso F G X e).hom = η[X ⊗ X] := by
  have : IsMonHom (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).hom :=
    inferInstanceAs (IsMonHom (Functor.LaxMonoidal.μ F (G.obj X) (G.obj X)))
  have : IsMonHom (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv := inferInstance
  change η[F.obj (G.obj X ⊗ G.obj X)] ≫
    (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv ≫ (e ⊗ᵢ e).inv = η[X ⊗ X]
  rw [← Category.assoc, IsMonHom.one_hom (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv]
  exact PointedTensorIsomorphism.pointedIso_tensor_inverse e he

variable [IsCommMonObj X]

theorem productMultiplicationTransport_point (he : η[X] ≫ e.hom = η[F.obj (G.obj X)]) :
    η[F.obj (G.obj X ⊗ G.obj X)] ≫ productMultiplicationTransport F G X e = η[F.obj (G.obj X)] := by
  change η[F.obj (G.obj X ⊗ G.obj X)] ≫
    (productMultiplicationTransportIso F G X e).hom ≫ μ[X] ≫ e.hom = η[F.obj (G.obj X)]
  rw [← Category.assoc, productMultiplicationTransportIso_point F G X e he,
    ← Category.assoc, IsMonHom.one_hom μ[X], he]

theorem productMultiplicationReference_point :
    η[F.obj (G.obj X ⊗ G.obj X)] ≫ productMultiplicationReference F G X = η[F.obj (G.obj X)] := by
  have : IsMonHom (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).hom :=
    inferInstanceAs (IsMonHom (Functor.LaxMonoidal.μ F (G.obj X) (G.obj X)))
  have : IsMonHom (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv := inferInstance
  change η[F.obj (G.obj X ⊗ G.obj X)] ≫
    (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv ≫ μ[F.obj (G.obj X)] = η[F.obj (G.obj X)]
  rw [← Category.assoc, IsMonHom.one_hom (Functor.Monoidal.μIso F (G.obj X) (G.obj X)).inv,
    IsMonHom.one_hom μ[F.obj (G.obj X)]]

theorem productMultiplicationTransport_identity (he : η[X] ≫ e.hom = η[F.obj (G.obj X)]) :
    η[F.obj (G.obj X ⊗ G.obj X)] ≫ productMultiplicationTransport F G X e =
      η[F.obj (G.obj X ⊗ G.obj X)] ≫ productMultiplicationReference F G X :=
  (productMultiplicationTransport_point F G X e he).trans (productMultiplicationReference_point F G X).symm

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TransportedMultiplicationIdentity
