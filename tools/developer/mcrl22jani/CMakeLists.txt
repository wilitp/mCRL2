if(MCRL2_ENABLE_BOOST_JSON_SUPPORT)

  mcrl2_add_tool(mcrl22jani
    SOURCES
      mcrl22jani.cpp
    DEPENDS
      mcrl2_lps
      mcrl2_lts
  )

endif()
