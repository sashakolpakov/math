import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramMapLaws

/-! # Presheaf Diagram Cone -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramCone

noncomputable section

/-! A genuine family of constant-presheaf frame maps assembles into
a map from the frame Čech total to the global presheaf Čech resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

private theorem inverse_square {A : Type*} [Category A]
    {V B C D E : A} (t : V ⟶ B) (t' : V ⟶ C) (e : D ≅ B) (e' : E ≅ C)
    (f : D ⟶ E) (b : B ⟶ C) (he : f ≫ e'.hom = e.hom ≫ b) (ht : t ≫ b = t') :
    (t ≫ e.inv) ≫ f = t' ≫ e'.inv := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he, Iso.inv_hom_id_assoc, ht]

universe u v d e r t
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type d} [Category.{e} D] (R : Type r) [CommRing R]
  {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{t} R) ℕ)
  (P : Cᵒᵖ ⥤ CochainComplex (Dᵒᵖ ⥤ ModuleCat.{t} R) ℕ)
  (a : Q ⋙ (Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ) ⟶ P)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.DiagramSectionCoordinates
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.TotalCup.CechProduct.total N (OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates.complex Q)
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.Total.CechConeTotal.total U P

def localMap (T : Dᵒᵖ) : Q ⟶ DiagramSectionCoordinates.diagram R P T where
  app V := ((DiagramSectionCoordinates.evaluation R T).mapHomologicalComplex (.up ℕ)).map (a.app V)
  naturality V W f := by
    exact congrArg ((DiagramSectionCoordinates.evaluation R T).mapHomologicalComplex (.up ℕ)).map (a.naturality f)

omit [HasBinaryProducts C] in
theorem localMap_natural {T T' : Dᵒᵖ} (α : T ⟶ T') :
    localMap R Q P a T ≫ DiagramSectionCoordinates.diagramMap R P α = localMap R Q P a T' := by
  apply NatTrans.ext
  funext V
  apply HomologicalComplex.Hom.ext
  funext q
  change ((a.app V).f q).app T ≫ ((P.obj V).X q).map α = ((a.app V).f q).app T'
  exact (((a.app V).f q).naturality α).symm.trans (Category.id_comp _)

def localTotalMap (T : Dᵒᵖ) : M ⟶
    ((DiagramSectionCoordinates.evaluation R T).mapHomologicalComplex (.up ℕ)).obj K :=
  ComplexDiagramNaturality.Coordinates.totalMap U (localMap R Q P a T) ≫
    (DiagramSectionCoordinates.totalIso R U P T).inv

theorem localTotalMap_natural {T T' : Dᵒᵖ} (α : T ⟶ T') :
    localTotalMap R U Q P a T ≫
      ((DiagramSectionCoordinates.evaluationMap R α).mapHomologicalComplex (.up ℕ)).app K =
        localTotalMap R U Q P a T' :=
  inverse_square
    (ComplexDiagramNaturality.Coordinates.totalMap U (localMap R Q P a T))
    (ComplexDiagramNaturality.Coordinates.totalMap U (localMap R Q P a T'))
    (DiagramSectionCoordinates.totalIso R U P T) (DiagramSectionCoordinates.totalIso R U P T')
    (((DiagramSectionCoordinates.evaluationMap R α).mapHomologicalComplex (.up ℕ)).app K)
    (DiagramSectionCoordinates.totalMap R U P α) (DiagramSectionCoordinates.total_natural R U P α)
    ((ComplexDiagramMapLaws.Coordinates.totalMap_comp U _ _).symm.trans
      (congrArg (ComplexDiagramNaturality.Coordinates.totalMap U) (localMap_natural R Q P a α)))

def map : ((Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ K where
  f q :=
    { app T := (localTotalMap R U Q P a T).f q
      naturality T T' α := by
        change 𝟙 _ ≫ (localTotalMap R U Q P a T').f q =
          (localTotalMap R U Q P a T).f q ≫ ((K).X q).map α
        exact (Category.id_comp _).trans
          (congrArg (fun f => f.f q) (localTotalMap_natural R U Q P a α)).symm }
  comm' i j _ := by
    apply NatTrans.ext
    funext T
    exact (localTotalMap R U Q P a T).comm i j

variable (μ : ∀ i j V, (Q.obj V).X i →ₗ[R] (Q.obj V).X j →ₗ[R] (Q.obj V).X (i+j))
  (ν : ∀ i j V T, ((P.obj V).X i).obj T →ₗ[R]
    ((P.obj V).X j).obj T →ₗ[R] ((P.obj V).X (i+j)).obj T)
  (ha : ∀ i j V T x y, ((a.app V).f (i+j)).app T (μ i j V x y) =
    ν i j V T (((a.app V).f i).app T x) (((a.app V).f j).app T y))

include ha in
theorem map_cup (i j : ℕ) (T : Dᵒᵖ) (x : (M).X i) (y : (M).X j) :
    ((PresheafDiagramCone.map R U Q P a).f (i+j)).app T
      (Presheaf.TotalCup.CechProduct.totalCup N (ComplexDiagramCoordinates.complex Q) μ i j x y) =
        PresheafDiagramProduct.pairing R U P ν i j T
          (((PresheafDiagramCone.map R U Q P a).f i).app T x) (((PresheafDiagramCone.map R U Q P a).f j).app T y) := by
  apply (asIso ((DiagramSectionCoordinates.totalIso R U P T).hom.f (i+j))).toLinearEquiv.injective
  have hn := Presheaf.CechProductNaturality.totalMap_pairing N μ
    (PresheafDiagramProduct.nativePairing R P ν T)
    (ComplexDiagramNaturality.Coordinates.complexMap (localMap R Q P a T))
    (fun i j V x y => ha i j V T x y) i j x y
  have hm (q : ℕ) (z : (M).X q) :
      (DiagramSectionCoordinates.totalIso R U P T).hom.f q (((PresheafDiagramCone.map R U Q P a).f q).app T z) =
        (ComplexDiagramNaturality.Coordinates.totalMap U (localMap R Q P a T)).f q z := by
    change (DiagramSectionCoordinates.totalIso R U P T).hom.f q
      ((DiagramSectionCoordinates.totalIso R U P T).inv.f q
        ((ComplexDiagramNaturality.Coordinates.totalMap U (localMap R Q P a T)).f q z)) = _
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.f q) (DiagramSectionCoordinates.totalIso R U P T).inv_hom_id) _
  change (DiagramSectionCoordinates.totalIso R U P T).hom.f (i+j) _ = (DiagramSectionCoordinates.totalIso R U P T).hom.f (i+j) _
  exact (hm _ _).trans (hn.trans
    ((congrArg₂
      (fun x y => Presheaf.TotalCup.CechProduct.totalCup N (DiagramSectionCoordinates.complex R P T)
        (PresheafDiagramProduct.nativePairing R P ν T) i j x y)
      (hm i x).symm (hm j y).symm).trans
      (Cochain.PairingTransport.hom_cup (DiagramSectionCoordinates.totalIso R U P T)
        (PresheafDiagramProduct.nativeCup R U P ν T) i j _ _).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafDiagramCone
