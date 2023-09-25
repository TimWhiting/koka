set(sources linear.kk nonlinear.kk linear_1.kk nonlinear_1.kk linear_2.kk nonlinear_2.kk linear_2_poly.kk nonlinear_2_poly.kk)

# find_program(kokadev "koka")

find_program(stack "stack" REQUIRED)
if(APPLE)
  set(koka ${stack} exec koka --)
else()
  set(koka ${stack} exec koka --)
endif()


foreach (source IN LISTS sources)
  get_filename_component(basename "${source}" NAME_WE)
  set(name    "${basename}")
  set(name_optimized    "${basename}_optimized")

  set(out_dir     "${CMAKE_CURRENT_BINARY_DIR}/out/bench")
  set(out_path    "${out_dir}/${name}")
  set(out_path_optimized    "${out_dir}/${name_optimized}")

  
  set(ccomp "gcc")
  
  add_custom_command(
    OUTPUT  ${out_path}
    COMMAND ${koka} --target=c --stack=128M --outputdir=${out_dir} --buildname=${name} -v -i$<SHELL_PATH:${CMAKE_CURRENT_SOURCE_DIR}> "${source}"
    DEPENDS ${source}
    VERBATIM)
  add_custom_command(
    OUTPUT  ${out_path_optimized}
    COMMAND ${koka} --target=c --stack=128M --outputdir=${out_dir} --buildname=${name_optimized} -v -O3 -i$<SHELL_PATH:${CMAKE_CURRENT_SOURCE_DIR}> "${source}"
    DEPENDS ${source}
    VERBATIM)

  add_custom_target(update-${name_optimized} ALL DEPENDS "${out_path_optimized}")
  add_executable(${name_optimized}-exe IMPORTED)
  set_target_properties(${name_optimized}-exe PROPERTIES IMPORTED_LOCATION "${out_path_optimized}")

  add_test(NAME ${name_optimized} COMMAND ${name_optimized}-exe)
  set_tests_properties(${name_optimized} PROPERTIES LABELS koka)

  add_custom_target(update-${name} ALL DEPENDS "${out_path}")
  add_executable(${name}-exe IMPORTED)
  set_target_properties(${name}-exe PROPERTIES IMPORTED_LOCATION "${out_path_optimized}")

  add_test(NAME ${name} COMMAND ${name}-exe)
  set_tests_properties(${name} PROPERTIES LABELS koka)
endforeach ()
