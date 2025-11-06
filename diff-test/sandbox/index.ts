import * as Y from "yjs";

const main = () => {
  const doc = new Y.Doc();

  const updateArr: Uint8Array[] = [];

  for (let i = 0; i < 10; i++) {
    const docTmp = new Y.Doc();
    docTmp.clientID = i;
    const ytext = docTmp.getText("text");
    ytext.insert(0, i.toString());
    const update = Y.encodeStateAsUpdate(docTmp);
    updateArr.push(update);
  }

  let updateA: Uint8Array;
  {
    const docA = new Y.Doc();
    Y.applyUpdate(docA, updateArr[4]);
    const ytext = docA.getText("text");
    console.log("docA text:", ytext.toString()); // Should print "14"

    ytext.insert(0, "A");
    console.log("docA text after insert:", ytext.toString()); // Should print "1A4"
    updateA = Y.encodeStateAsUpdate(docA);
  }

  let updateB: Uint8Array;
  {
    const docB = new Y.Doc();
    Y.applyUpdate(docB, updateArr[6]);
    Y.applyUpdate(docB, updateArr[8]);
    const ytext = docB.getText("text");
    console.log("docB text:", ytext.toString()); // Should print "68"

    ytext.insert(1, "B");
    console.log("docB text after insert:", ytext.toString()); // Should print "6B8"
    updateB = Y.encodeStateAsUpdate(docB);
  }

  let updateC: Uint8Array;
  {
    const docC = new Y.Doc();
    Y.applyUpdate(docC, updateArr[3]);
    Y.applyUpdate(docC, updateArr[9]);
    const ytext = docC.getText("text");
    console.log("docC text:", ytext.toString()); // Should print "39"
    ytext.insert(1, "C");
    console.log("docC text after insert:", ytext.toString()); // Should print "3C9"
    updateC = Y.encodeStateAsUpdate(docC);
  }

  {
    const docABC = new Y.Doc();
    updateArr.forEach((update) => {
      Y.applyUpdate(docABC, update);
    });
    Y.applyUpdate(docABC, updateA);
    Y.applyUpdate(docABC, updateB);
    Y.applyUpdate(docABC, updateC);
    const ytextABC = docABC.getText("text");
    console.log("docABC text:", ytextABC.toString());
  }

  {
    const docCBA = new Y.Doc();
    updateArr.forEach((update) => {
      Y.applyUpdate(docCBA, update);
    });
    Y.applyUpdate(docCBA, updateC);
    Y.applyUpdate(docCBA, updateB);
    Y.applyUpdate(docCBA, updateA);
    const ytextCBA = docCBA.getText("text");
    console.log("docCBA text:", ytextCBA.toString());
  }
};

main();
