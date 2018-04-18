$(function() {
  var H = 26;
  var R1 = 6;
  var R2 = 14;

  var createLink = function($img, row, modelName) {
    var imgPos = $img.position();
    var imgPadLeft = ($img.innerWidth() - $img.width())/2 + 1;
    var imgPadTop = ($img.innerHeight() - $img.height())/2;
    var $parDiv = $img.parent();
    var $a = $('<a href="models/hol/' + modelName + '.html"></a>');
    var vMargin = 2;
    var indent = 40;
    $a.addClass("overlayModelLink");
    var a = $a.get(0);
    a.style["width"] = $img.width() - indent + "px";
    a.style["height"] = H - 2*vMargin + "px";
    var left = imgPos.left + imgPadLeft + indent + "px";
    a.style["left"] = left;
    var top = imgPos.top + imgPadTop + row*H + "px";
    a.style["top"] = top;
    $parDiv.append($a);
  };

  var img1 = $("#models-graph-margrave");
  var img2 = $("#models-synth");
  
  createLink(img1, 1, "graph/graph.als");
  createLink(img1, 2, "graph/micro_benchmarks.als");
  createLink(img1, 3, "graph/turan.als");
  createLink(img1, 5, "margrave/gradePolicy.als");

  createLink(img2, 1, "sygus/array_search.als");
  for (var i = 2; i <= 5; i++) createLink(img2, 2 + i - 2, "sygus/array_search_" + i + ".als");
  createLink(img2, 6, "sygus/max.als");
  for (var i = 3; i <= 8; i++) createLink(img2, 7 + i - 3, "sygus/max-" + i + ".als");
  createLink(img2, 13, "sygus/synth.als");
});
