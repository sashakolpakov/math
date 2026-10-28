import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MapFunctor

/-! # Functorial Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.FunctorialMap.FirstThreeFunctorialMap

noncomputable section

/-! Actual cochain maps across additive functors restrict to the first three
terms, compatibly with the original projections and commuting squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]
  {K K' : CochainComplex C ℕ} {L L' : CochainComplex D ℕ}
  (f : (F.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def map : (F.mapHomologicalComplex (.up ℕ)).obj (ThreeComplex.FirstThreeComplex.complex K) ⟶
    ThreeComplex.FirstThreeComplex.complex L :=
  (MapFunctor.FirstThreeMapFunctor.iso F K).hom ≫ ThreeComplex.FirstThreeComplex.map f

@[simp] theorem map_zero : (FirstThreeFunctorialMap.map F f).f 0 = f.f 0 := Category.id_comp _
@[simp] theorem map_one : (FirstThreeFunctorialMap.map F f).f 1 = f.f 1 := Category.id_comp _
@[simp] theorem map_two : (FirstThreeFunctorialMap.map F f).f 2 = f.f 2 := Category.id_comp _

theorem projection_square :
    (F.mapHomologicalComplex (.up ℕ)).map (ThreeComplex.FirstThreeComplex.projection K) ≫ FirstThreeFunctorialMap.map F f =
      f ≫ ThreeComplex.FirstThreeComplex.projection L := by
  change _ ≫ ((MapFunctor.FirstThreeMapFunctor.iso F K).hom ≫ ThreeComplex.FirstThreeComplex.map f) = _
  rw [← Category.assoc, MapFunctor.FirstThreeMapFunctor.projection, ThreeComplex.FirstThreeComplex.projection_naturality]

variable (f' : (F.mapHomologicalComplex (.up ℕ)).obj K' ⟶ L')
  (a : K ⟶ K') (b : L ⟶ L')
  (h : (F.mapHomologicalComplex (.up ℕ)).map a ≫ f' = f ≫ b)

include h in
theorem naturality :
    (F.mapHomologicalComplex (.up ℕ)).map (ThreeComplex.FirstThreeComplex.map a) ≫ FirstThreeFunctorialMap.map F f' =
      FirstThreeFunctorialMap.map F f ≫ ThreeComplex.FirstThreeComplex.map b := by
  apply HomologicalComplex.Hom.ext
  funext n
  rcases n with _ | (_ | (_ | n))
  · change F.map (a.f 0) ≫ (𝟙 _ ≫ f'.f 0) = (𝟙 _ ≫ f.f 0) ≫ b.f 0
    erw [Category.id_comp, Category.id_comp]
    exact congrArg (fun t => t.f 0) h
  · change F.map (a.f 1) ≫ (𝟙 _ ≫ f'.f 1) = (𝟙 _ ≫ f.f 1) ≫ b.f 1
    erw [Category.id_comp, Category.id_comp]
    exact congrArg (fun t => t.f 1) h
  · change F.map (a.f 2) ≫ (𝟙 _ ≫ f'.f 2) = (𝟙 _ ≫ f.f 2) ≫ b.f 2
    erw [Category.id_comp, Category.id_comp]
    exact congrArg (fun t => t.f 2) h
  · exact (isZero_zero D).eq_of_tgt _ _

variable {M M' : CochainComplex D ℕ} {N N' : CochainComplex C ℕ}
  (g : M ⟶ (F.mapHomologicalComplex (.up ℕ)).obj N)

def direct : ThreeComplex.FirstThreeComplex.complex M ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj (ThreeComplex.FirstThreeComplex.complex N) :=
  ThreeComplex.FirstThreeComplex.map g ≫ (MapFunctor.FirstThreeMapFunctor.iso F N).inv

@[simp] theorem direct_zero : (direct F g).f 0 = g.f 0 := Category.comp_id _
@[simp] theorem direct_one : (direct F g).f 1 = g.f 1 := Category.comp_id _
@[simp] theorem direct_two : (direct F g).f 2 = g.f 2 := Category.comp_id _

theorem direct_projection : ThreeComplex.FirstThreeComplex.projection M ≫ direct F g =
    g ≫ (F.mapHomologicalComplex (.up ℕ)).map (ThreeComplex.FirstThreeComplex.projection N) := by
  change _ ≫ (ThreeComplex.FirstThreeComplex.map g ≫ (MapFunctor.FirstThreeMapFunctor.iso F N).inv) = _
  rw [← Category.assoc, ThreeComplex.FirstThreeComplex.projection_naturality, Category.assoc,
    ← MapFunctor.FirstThreeMapFunctor.projection F N, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (g' : M' ⟶ (F.mapHomologicalComplex (.up ℕ)).obj N')
  (c : M ⟶ M') (d : N ⟶ N')
  (hd : c ≫ g' = g ≫ (F.mapHomologicalComplex (.up ℕ)).map d)

include hd in
theorem direct_naturality :
    ThreeComplex.FirstThreeComplex.map c ≫ direct F g' =
      direct F g ≫ (F.mapHomologicalComplex (.up ℕ)).map (ThreeComplex.FirstThreeComplex.map d) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rcases n with _ | (_ | (_ | n))
  · change c.f 0 ≫ (g'.f 0 ≫ 𝟙 _) = (g.f 0 ≫ 𝟙 _) ≫ F.map (d.f 0)
    erw [Category.comp_id, Category.comp_id]
    exact congrArg (fun t => t.f 0) hd
  · change c.f 1 ≫ (g'.f 1 ≫ 𝟙 _) = (g.f 1 ≫ 𝟙 _) ≫ F.map (d.f 1)
    erw [Category.comp_id, Category.comp_id]
    exact congrArg (fun t => t.f 1) hd
  · change c.f 2 ≫ (g'.f 2 ≫ 𝟙 _) = (g.f 2 ≫ 𝟙 _) ≫ F.map (d.f 2)
    erw [Category.comp_id, Category.comp_id]
    exact congrArg (fun t => t.f 2) hd
  · exact (F.map_isZero (isZero_zero C)).eq_of_tgt _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.FunctorialMap.FirstThreeFunctorialMap
