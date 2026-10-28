import OAI.AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.InverseHom

/-! # Shifted Inverse -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.ShiftedInverse.ShiftedInverseTransport

/-! Transport of shifted cohomology classes respects an actual commuting square of isomorphisms. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]
  {A K K' : C} {B L L' : D} (s : F.obj A ≅ B) (e : K ≅ K') (d : L ≅ L')
  (a : F.obj K ⟶ L) (b : F.obj K' ⟶ L')
  (h : F.map e.hom ≫ b = a ≫ d.hom)

include h in
theorem naturality (n : ℤ) (x : A ⟶ K'⟦n⟧) :
    AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport F s b x ≫ d.inv⟦n⟧' =
      AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport F s a (x ≫ e.inv⟦n⟧') := by
  have hi : b ≫ d.inv = F.map e.inv ≫ a :=
    InverseHom.InverseHomCongr.inverse_square (F.mapIso e) d a b h
  have hm : ShiftedHom.map (x ≫ e.inv⟦n⟧') F =
      ShiftedHom.map x F ≫ (F.map e.inv)⟦n⟧' := by
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using
      ShiftedHom.map_comp x (ShiftedHom.mk₀ (0 : ℤ) rfl e.inv) (zero_add n) F
  dsimp only [AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport]
  rw [hm]
  simp only [Category.assoc]
  rw [← (shiftFunctor D n).map_comp, hi, (shiftFunctor D n).map_comp]

end NumberTheory.PadicHodge.GeometricComparison.ShiftedInverse.ShiftedInverseTransport

namespace NumberTheory.PadicHodge.GeometricComparison.ShiftedInverse.ShiftedMapSquare

/-! An actual commuting square induces a commuting square on shifted classes,
without assuming that the vertical maps are isomorphisms. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]
  {A K K' : C} {B L L' : D} (s : F.obj A ≅ B) (e : K ⟶ K') (d : L ⟶ L')
  (a : F.obj K ⟶ L) (b : F.obj K' ⟶ L')
  (h : F.map e ≫ b = a ≫ d)

include h in
theorem naturality (n : ℤ) (x : A ⟶ K⟦n⟧) :
    AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport F s b (x ≫ e⟦n⟧') =
      AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport F s a x ≫ d⟦n⟧' := by
  have hm : ShiftedHom.map (x ≫ e⟦n⟧') F =
      ShiftedHom.map x F ≫ (F.map e)⟦n⟧' := by
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using
      ShiftedHom.map_comp x (ShiftedHom.mk₀ (0 : ℤ) rfl e) (zero_add n) F
  dsimp only [AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare.transport]
  rw [hm]
  simp only [Category.assoc]
  rw [← (shiftFunctor D n).map_comp, h, (shiftFunctor D n).map_comp]

end NumberTheory.PadicHodge.GeometricComparison.ShiftedInverse.ShiftedMapSquare

end

end OAI
