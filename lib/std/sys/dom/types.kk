/*----------------------------------------------------------------------------
   Copyright 2012-2021, Microsoft Research, Daan Leijen.
  
   Licensed under the Apache License, Version 2.0 ("The Licence"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/

// Basic types of the HTML5 DOM model
pub module std/sys/dom/types

/* Effect primitives */
pub type hdom :: H
pub alias dom = <exn,ndet,console,net,ui,st<hdom>>

/* Type aliases */
pub type date
pub alias timestamp = date
pub alias abstractView = any
pub alias domTimeStamp = date
// pub alias float32 = double
// pub alias float64 = double
pub alias byte = uint8
pub alias longlong = int
pub alias octet = int
pub alias unsignedlonglong = int
// pub alias int32 = int
pub alias int8 = int
pub alias milliseconds = int
pub alias uint16 = int
pub alias uint32 = int
pub alias uint8 = int
pub alias windowTimers = window

/* Enum declarations */
pub type applicationCacheStatus {
  UNCACHED
  IDLE
  CHECKING
  DOWNLOADING
  UPDATEREADY
  OBSOLETE
}
pub type cssPrimitiveType {
  CSS_UNKNOWN
  CSS_NUMBER
  CSS_PERCENTAGE
  CSS_EMS
  CSS_EXS
  CSS_PX
  CSS_CM
  CSS_MM
  CSS_IN
  CSS_PT
  CSS_PC
  CSS_DEG
  CSS_RAD
  CSS_GRAD
  CSS_MS
  CSS_S
  CSS_HZ
  CSS_KHZ
  CSS_DIMENSION
  CSS_STRING
  CSS_URI
  CSS_IDENT
  CSS_ATTR
  CSS_COUNTER
  CSS_RECT
  CSS_RGBCOLOR
  CSS_UNICODE_RANGE
}
pub type cssRuleType {
  STYLE_RULE
  IMPORT_RULE
  MEDIA_RULE
  FONT_FACE_RULE
  PAGE_RULE
  NAMESPACE_RULE
}
pub type cssValueType {
  CSS_INHERIT
  CSS_PRIMITIVE_VALUE
  CSS_VALUE_LIST
  CSS_CUSTOM
}
pub type documentPosition {
  DOCUMENT_POSITION_DISCONNECTED
  DOCUMENT_POSITION_PRECEDING
  DOCUMENT_POSITION_FOLLOWING
  DOCUMENT_POSITION_CONTAINS
  DOCUMENT_POSITION_CONTAINED_BY
  DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC
}
pub type domException {
  INDEX_SIZE_ERR
  DOMSTRING_SIZE_ERR
  HIERARCHY_REQUEST_ERR
  WRONG_DOCUMENT_ERR
  INVALID_CHARACTER_ERR
  NO_DATA_ALLOWED_ERR
  NO_MODIFICATION_ALLOWED_ERR
  NOT_FOUND_ERR
  NOT_SUPPORTED_ERR
  INUSE_ATTRIBUTE_ERR
  INVALID_STATE_ERR
  SYNTAX_ERR
  INVALID_MODIFICATION_ERR
  NAMESPACE_ERR
  INVALID_ACCESS_ERR
  VALIDATION_ERR
  TYPE_MISMATCH_ERR
  SECURITY_ERR
  NETWORK_ERR
  ABORT_ERR
  URL_MISMATCH_ERR
  QUOTA_EXCEEDED_ERR
  TIMEOUT_ERR
  INVALID_NODE_TYPE_ERR
  DATA_CLONE_ERR
}
pub type eventExceptionCode {
  UNSPECIFIED_EVENT_TYPE_ERR
  DISPATCH_REQUEST_ERR
}
pub type eventPhase {
  CAPTURING_PHASE
  AT_TARGET
  BUBBLING_PHASE
}
pub type eventSourceReadyState {
  CONNECTING
  OPEN
  CLOSED
}
pub type fileErrorCode {
  FILE__NOT_FOUND_ERR
  FILE__SECURITY_ERR
  FILE__ABORT_ERR
  FILE__NOT_READABLE_ERR
  FILE__ENCODING_ERR
}
pub type fileExceptionCode {
  FILE_NOT_FOUND_ERR
  FILE_SECURITY_ERR
  FILE_ABORT_ERR
  FILE_NOT_READABLE_ERR
  FILE_ENCODING_ERR
  BYTES_PER_ELEMENT
}
pub type fileReaderReadyState {
  FILE_READER_EMPTY
  FILE_READER_LOADING
  FILE_READER_DONE
}
pub type keyboardEventLocation {
  DOM_KEY_LOCATION_STANDARD
  DOM_KEY_LOCATION_LEFT
  DOM_KEY_LOCATION_RIGHT
  DOM_KEY_LOCATION_NUMPAD
  DOM_KEY_LOCATION_MOBILE
  DOM_KEY_LOCATION_JOYSTICK
}
pub type mediaErrorCode {
  MEDIA_ERR_ABORTED
  MEDIA_ERR_NETWORK
  MEDIA_ERR_DECODE
  MEDIA_ERR_SRC_NOT_SUPPORTED
}
pub type mediaReadyState {
  HAVE_NOTHING
  HAVE_METADATA
  HAVE_CURRENT_DATA
  HAVE_FUTURE_DATA
  HAVE_ENOUGH_DATA
}
pub type mediaStreamReadyState {
  LIVE
  ENDED
}
pub type mutationEventAttrChange {
  MODIFICATION
  ADDITION
  REMOVAL
}
pub type navigatorUserMediaErrorCode {
  PERMISSION_DENIED
}
pub type networkState {
  NETWORK_EMPTY
  NETWORK_IDLE
  NETWORK_LOADING
  NETWORK_NO_SOURCE
}
pub type nodeFilterAcceptCode {
  FILTER_ACCEPT
  FILTER_REJECT
  FILTER_SKIP
}
pub type nodeFilterSelectCode {
  SHOW_ALL
  SHOW_ELEMENT
  SHOW_ATTRIBUTE
  SHOW_TEXT
  SHOW_CDATA_SECTION
  SHOW_ENTITY_REFERENCE
  SHOW_ENTITY
  SHOW_PROCESSING_INSTRUCTION
  SHOW_COMMENT
  SHOW_DOCUMENT
  SHOW_DOCUMENT_TYPE
  SHOW_DOCUMENT_FRAGMENT
  SHOW_NOTATION
}
pub type nodeType {
  ELEMENT_NODE
  ATTRIBUTE_NODE
  TEXT_NODE
  CDATA_SECTION_NODE
  ENTITY_REFERENCE_NODE
  ENTITY_NODE
  PROCESSING_INSTRUCTION_NODE
  COMMENT_NODE
  DOCUMENT_NODE
  DOCUMENT_TYPE_NODE
  DOCUMENT_FRAGMENT_NODE
  NOTATION_NODE
}
pub type peerConnectionReadyState {
  PEER_CONNECTION_NEW
  PEER_CONNECTION_NEGOTIATING
  PEER_CONNECTION_ACTIVE
  PEER_CONNECTION_CLOSED
}
pub type rangeExceptionCode {
  RANGE_BAD_BOUNDARYPOINTS_ERR
  RANGE_INVALID_NODE_TYPE_ERR
}
pub type rangeExceptionCompareHow {
  START_TO_START
  START_TO_END
  END_TO_END
  END_TO_START
}
pub type textEventInputMethod {
  DOM_INPUT_METHOD_UNKNOWN
  DOM_INPUT_METHOD_KEYBOARD
  DOM_INPUT_METHOD_PASTE
  DOM_INPUT_METHOD_DROP
  DOM_INPUT_METHOD_IME
  DOM_INPUT_METHOD_OPTION
  DOM_INPUT_METHOD_HANDWRITING
  DOM_INPUT_METHOD_VOICE
  DOM_INPUT_METHOD_MULTIMODAL
  DOM_INPUT_METHOD_SCRIPT
}
pub type textTrackMode {
  TEXT_TRACK_OFF
  TEXT_TRACK_HIDDEN
  TEXT_TRACK_SHOWING
}
pub type textTrackReadyState {
  TEXT_TRACK_NONE
  TEXT_TRACK_LOADING
  TEXT_TRACK_LOADED
  TEXT_TRACK_ERROR
}
pub type wheelEventDeltaMode {
  DOM_DELTA_PIXEL
  DOM_DELTA_LINE
  DOM_DELTA_PAGE
}
pub type xmlHttpRequestReadyState {
  UNSENT
  OPENED
  HEADERS_RECEIVED
  LOADING
  DONE
}

/* Abstract type declarations for interfaces */
pub type styleSheetList
inline extern get : (this: styleSheetList, index: int) -> dom cssStyleSheet
{ inline "(#1)[#2]" }
inline extern set : (this: styleSheetList, index: int, assigned: cssStyleSheet) -> dom ()
{ inline "((#1)[#2] = #3)" }
inline extern length : (this: styleSheetList) -> dom int
{ inline "(#1).length" }
pub type windowBase64
pub type windowProxy
pub type seqence // used in `initMessageEvent` and `postMessage`
pub type anonXmlHttpRequest
pub type applicationCache
pub type arrayBuffer
pub type arrayBufferView
pub type attr
pub type audioTrack
pub type audioTrackList
pub type barProp
pub type beforeUnloadEvent
pub type blob
pub type blobCallback
pub type booleanArray
pub type byteArray
pub type css2Properties
pub type cssCharsetRule
pub type cssColorComponentValue
pub type cssComponentValue
pub type cssFontFaceRule
pub type cssIdentifierComponentValue
pub type cssImportRule
pub type cssKeywordComponentValue
pub type cssLengthComponentValue
pub type cssMapValue
pub type cssMediaRule
pub type cssNamespaceRule
pub type cssPageRule
pub type cssPercentageComponentValue
pub type cssPrimitiveValue
pub type cssPropertyValue
pub type cssPropertyValueList
pub type cssRule
pub type cssStringComponentValue
pub type cssStyleDeclaration
pub type cssStyleDeclarationValue
pub type cssStyleRule
pub type cssStyleSheet
pub type cssUrlComponentValue
pub type cssUnknownRule
pub type cssValue
pub type cssValueList
pub type canvasGradient
pub type canvasPattern
pub type canvasPixelArray
pub type canvasRenderingContext2d
pub type caretPosition
pub type characterData
pub type clientRect
pub type clientRectList
pub type comment
pub type compositionEvent
pub type counter
pub type customEvent
pub type customEventInit
pub type domElementMap
pub type domImplementation
pub type domImplementationCss
pub type domSettableTokenList
pub type domStringList
pub type domStringMap
pub type domTokenList
pub type dataTransfer
pub type dataTransferItem
pub type dataTransferItemList
pub type dataView
pub type document
pub type documentCss
pub type documentFragment
pub type documentRange
pub type documentTraversal
pub type documentType
pub type doubleArray
pub type dragEvent
pub type element
pub type elementCssInlineStyle
pub type event
pub type eventInit
pub type eventListener
pub type eventSource
pub type eventTarget
pub type external_
pub type file
pub type fileCallback
pub type fileError
pub type fileList
pub type fileReader
pub type fileReaderSync
pub type float32Array
pub type float64Array
pub type floatArray
pub type focusEvent
pub type formData
pub type functionStringCallback
pub type htmlAllCollection
pub type htmlAnchorElement
pub type htmlAppletElement
pub type htmlAreaElement
pub type htmlAudioElement
pub type htmlBrElement
pub type htmlBaseElement
pub type htmlBaseFontElement
pub type htmlBodyElement
pub type htmlButtonElement
pub type htmlCanvasElement
pub type htmlCollection
pub type htmlCommandElement
pub type htmlDListElement
pub type htmlDataListElement
pub type htmlDetailsElement
pub type htmlDirectoryElement
pub type htmlDivElement
pub type htmlDocument
pub type htmlElement
pub type htmlEmbedElement
pub type htmlFieldSetElement
pub type htmlFontElement
pub type htmlFormControlsCollection
pub type htmlFormElement
pub type htmlFrameElement
pub type htmlFrameSetElement
pub type htmlHrElement
pub type htmlHeadElement
pub type htmlHeadingElement
pub type htmlHtmlElement
pub type htmlIframeElement
pub type htmlImageElement
pub type htmlInputElement
pub type htmlKeygenElement
pub type htmlLiElement
pub type htmlLabelElement
pub type htmlLegendElement
pub type htmlLinkElement
pub type htmlMapElement
pub type htmlMarqueeElement
pub type htmlMediaElement
pub type htmlMenuElement
pub type htmlMetaElement
pub type htmlMeterElement
pub type htmlModElement
pub type htmlOListElement
pub type htmlObjectElement
pub type htmlOptGroupElement
pub type htmlOptionElement
pub type htmlOptionsCollection
pub type htmlOutputElement
pub type htmlParagraphElement
pub type htmlParamElement
pub type htmlPreElement
pub type htmlProgressElement
pub type htmlPropertiesCollection
pub type htmlQuoteElement
pub type htmlScriptElement
pub type htmlSelectElement
pub type htmlSourceElement
pub type htmlSpanElement
pub type htmlStyleElement
pub type htmlTableCaptionElement
pub type htmlTableCellElement
pub type htmlTableColElement
pub type htmlTableDataCellElement
pub type htmlTableElement
pub type htmlTableHeaderCellElement
pub type htmlTableRowElement
pub type htmlTableSectionElement
pub type htmlTextAreaElement
pub type htmlTimeElement
pub type htmlTitleElement
pub type htmlTrackElement
pub type htmlUListElement
pub type htmlUnknownElement
pub type htmlVideoElement
pub type hashChangeEvent
pub type history
pub type imageData
pub type int16Array
pub type int32Array
pub type int8Array
pub type keyboardEvent
pub type linkStyle
pub type localMediaStream
pub type location
pub type longArray
pub type longLongArray
pub type mediaController
pub type mediaError
pub type mediaList
pub type mediaQueryList
pub type mediaQueryListListener
pub type mediaStream
pub type mediaStreamRecorder
pub type messageChannel
pub type messageEvent
pub type messagePort
pub type mouseEvent
pub type mutableTextTrack
pub type mutationEvent
pub type mutationNameEvent
pub type navigator
pub type navigatorUserMediaError
pub type navigatorUserMediaErrorCallback
pub type navigatorUserMediaSuccessCallback
pub type node
pub type nodeFilter
pub type nodeIterator
pub type nodeList
pub type octetArray
pub type pageTransitionEvent
pub type peerConnection
pub type popStateEvent
pub type processingInstruction
pub type progressEvent
pub type propertyNodeList
pub type rgbColor
pub type radioNodeList
pub type range
pub type rect
pub type screen
pub type shortArray
pub type signalingCallback
pub type streamEvent
pub type streamTrack
pub type styleSheet
pub type text
pub type textEvent
pub type textMetrics
pub type textTrack
pub type textTrackCue
pub type textTrackCueList
pub type timeRanges
pub type transferable
pub type treeWalker
pub type uiEvent
pub type uint16Array
pub type uint32Array
pub type uint8Array
pub type undoManager
pub type undoManagerEvent
pub type unsignedByteArray
pub type unsignedLongArray
pub type unsignedLongLongArray
pub type unsignedShortArray
pub type validityState
pub type videoTrack
pub type videoTrackList
pub type wheelEvent
pub type window
pub type windowModal
pub type xmlHttpRequest
pub type xmlHttpRequestEventTarget
pub type xmlHttpRequestUpload
